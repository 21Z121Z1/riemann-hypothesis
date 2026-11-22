import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3386
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2652
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3156
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3258
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2348
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3428
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2346
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusFlagUnitWeightBundlesNef
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3361
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2951
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3434
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToRigidifiedExtensionBijectivePNilpotent
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem bijective_of_isCan_of_isNilpotent_of_hodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (L : primDR A →ₗ[R] G.RigExt), (∀ c, IsCan t c (L c)) → Function.Bijective L := by
  intro hH p _ R _ hnil A _ g hA hg G t L hL
  obtain ⟨N, hN⟩ := hnil
  obtain ⟨hF, hHo, -⟩ := GlobalTheory.abelianDeRham_free_hodge_baseChange hH
  obtain ⟨hAll, -⟩ := hF R A g hA hg
  obtain ⟨hLie, hCompl, hFfin, hFproj, -⟩ := hHo R A g hA hg
  have hO : Function.Surjective (toH1O (A.hom ≫ 𝟙 _)) :=
    GlobalTheory.PtExt.toH1O_surjective_of_abelian hH R A g hA hg
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_hodgeFiltration_to_pDivOmega_linearMap p R N hN A hA G t

  haveI : Module.Finite R (Cot R (G.A N)) := .of_surjective _ (AugCot.d_surjective _)
  haveI : Module.Finite R G.omega :=
    .equiv (LinearEquiv.ofBijective _
      (PDivGroup.omegaLevel_bijective_of_pow_eq_zero p R N hN G N le_rfl)).symm
  haveI : Module.Projective R (PrimitiveSubmodule A) := hFproj

  have hψs : Function.Surjective ψ :=
    GlobalTheory.surjective_of_range_sup_smul_top_eq_top R _ G.omega ψ
      (GlobalTheory.T.primitive_hodge_to_omega_span_mod_maximal hH p R N hN A g hA hg G t ψ hψ)
  have hψi : Function.Injective ψ := by
    refine GlobalTheory.injective_of_dualMap_surjective_of_projective R _ G.omega ψ fun l => ?_
    obtain ⟨x, hx⟩ := GlobalTheory.T.exists_lie_comp_hodgeToOmega_eq_linearForm p R N hN A hA hLie hCompl G t ψ hψ l
    exact ⟨x, LinearMap.ext fun c => hx c⟩

  have hLF : ∀ c : PrimitiveSubmodule A, L c.1 = G.rigOfOmega (ψ c) := fun c =>
    GlobalTheory.PtExt.isCan_unique R A p G t c.1 hA _ _ (hL c.1) (hψ c)
  refine ⟨(injective_iff_map_eq_zero L).2 fun c hc => ?_, fun x => ?_⟩
  · have hcF : c ∈ PrimitiveSubmodule A :=
      GlobalTheory.T.mem_primitiveSubmodule_of_isCan_of_rigToExt_eq_zero p R N hN A hA G t c (L c) (hL c) (by rw [hc, map_zero])
    have h1 : G.rigOfOmega (ψ ⟨c, hcF⟩) = 0 := by rw [← hLF ⟨c, hcF⟩]; exact hc
    have h2 : ψ ⟨c, hcF⟩ = 0 :=
      PDivGroup.rigOfOmega_injective_of_pow p R N hN G (by rw [h1, map_zero])
    have h3 : (⟨c, hcF⟩ : PrimitiveSubmodule A) = 0 := hψi (by rw [h2, map_zero])
    exact congrArg Subtype.val h3
  · obtain ⟨c, x', hcx', hx'⟩ := GlobalTheory.T.exists_deRham_class_of_rigidified_extension p R N hN A hA hAll hO G t x
    have hx'L : x' = L c := GlobalTheory.PtExt.isCan_unique R A p G t c hA _ _ hcx' (hL c)
    have hd : G.rigToExt (x - L c) = 0 := by rw [map_sub, ← hx'L, hx', sub_self]
    obtain ⟨w, hw⟩ := (G.exact_rigOfOmega_rigToExt (x - L c)).1 hd
    obtain ⟨c₁, rfl⟩ := hψs w
    refine ⟨c + c₁.1, ?_⟩
    rw [map_add, hLF c₁, hw, add_sub_cancel]

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerCompat
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

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KSAgree

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (h₃ : W ≤ U) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom x) =
      (X.presheaf.map (homOfLE h₃).op).hom x := by
  show (X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom x = _
  rw [← Functor.map_comp]
  rfl

theorem res_comp {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (h₃ : W ≤ U) :
    (X.presheaf.map (homOfLE h₂).op).hom.comp (X.presheaf.map (homOfLE h₁).op).hom =
      (X.presheaf.map (homOfLE h₃).op).hom :=
  RingHom.ext (res_res h₁ h₂ h₃)

theorem der_compat {X : Scheme.{0}} (U : X.affineOpens) (f : Γ(X, U.1)) (P : X.Opens)
    (hP : P ≤ X.basicOpen f) (hPU : P ≤ U.1) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1))
    (DW : Derivation ℤ Γ(X, X.basicOpen f) Γ(X, X.basicOpen f)) (DP : Derivation ℤ Γ(X, P) Γ(X, P))
    (hW : ∀ r, DW ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom r) =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom (D r))
    (hD : ∀ r, DP ((X.presheaf.map (homOfLE hPU).op).hom r) = (X.presheaf.map (homOfLE hPU).op).hom (D r)) :
    ∀ r, DP ((X.presheaf.map (homOfLE hP).op).hom r) = (X.presheaf.map (homOfLE hP).op).hom (DW r) := by
  intro r
  obtain ⟨u, r', hu, hb⟩ := GlobalTheory.LogKSLoc.exists_frac U (X.affineBasicOpen f) (X.basicOpen_le f) f rfl r
  have key : ∀ x : Γ(X, U.1), DP ((X.presheaf.map (homOfLE hP).op).hom
      ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom x)) =
      (X.presheaf.map (homOfLE hP).op).hom (DW ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom x)) := by
    intro x
    rw [res_res _ _ hPU, hD, hW, res_res _ _ hPU]
  exact GlobalTheory.LogKSLoc.leibniz_frac _ DP (fun x y => by rw [DP.leibniz, smul_eq_mul, smul_eq_mul]) DW hu hb
    (key u) (key r')

theorem dual_alg {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') :
    (dualMap r).comp (algebraMap S (DualNumber S)) = (algebraMap S' (DualNumber S')).comp r := by
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl] <;> rfl

theorem fst_dual {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') :
    (TrivSqZeroExt.fstHom S' S' S').toRingHom.comp (dualMap r) = r.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext a <;> (try simp [dualMap]) <;> rfl

theorem dual_eps {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') (c : S) :
    (dualMap r).comp (epsMul c) = (epsMul (r c)).comp (dualMap r) := by
  ext a <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl] <;> rfl

section Gen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

theorem eps_over {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X}
    (hx : spMap r ≫ x = x') :
    spMap (dualMap r) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap S' (DualNumber S')) ≫ x' := by
  rw [← hx, ← Category.assoc, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.spMap_comp', dual_alg]

def epsHom {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X}
    (hx : spMap r ≫ x = x') : tEpsG x' ⟶ tEpsG x :=
  Over.homMk (spMap (dualMap r)) (eps_over r hx)

theorem tan_map {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X}
    (hx : spMap r ≫ x = x') {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    IsTanAtG t x' (spMap (dualMap r) ≫ v) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, hv.1, eps_over r hx]
  · have h : spMap (TrivSqZeroExt.fstHom S' S' S').toRingHom ≫ spMap (dualMap r) =
        spMap r ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
      rw [GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.spMap_comp', fst_dual]
    rw [← Category.assoc, h, Category.assoc, hv.2]
    let k : Over.mk x' ⟶ Over.mk x := Over.homMk (spMap r) hx
    exact congrArg CommaMorphism.left (comp_one k (M := t.G))

theorem comb_map {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X}
    (hx : spMap r ≫ x = x') {n : ℕ} {v : Fin n → (Sp (DualNumber S) ⟶ t.G.left)} {cf : Fin n → S}
    {w : Sp (DualNumber S) ⟶ t.G.left} (h : IsCombAtG t x v cf w) :
    IsCombAtG t x' (fun i => spMap (dualMap r) ≫ v i) (fun i => r (cf i)) (spMap (dualMap r) ≫ w) := by
  obtain ⟨u, hu, hw⟩ := h
  let φ : (tEpsG x ⟶ t.G) →* (tEpsG x' ⟶ t.G) :=
    { toFun := fun a => epsHom r hx ≫ a
      map_one' := comp_one _
      map_mul' := fun a b => comp_mul _ _ _ }
  refine ⟨fun i => φ (u i), fun i => ?_, ?_⟩
  · show spMap (dualMap r) ≫ (u i).left = _
    rw [hu, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp', dual_eps, ← GlobalTheory.LogKSLoc.spMap_comp', Category.assoc]
  · have e : (List.ofFn fun i => φ (u i)).prod = φ (List.ofFn u).prod := by
      rw [map_list_prod, List.map_ofFn]
      rfl
    rw [e, ← hw]
    rfl
end Gen

theorem tan_res : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (v : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left), IsTanAtG t (chart U) v → IsTanAtG t (chart W) (spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v) :=
  fun _ _ _ _ _ _ t U W hW _ hv => tan_map t _ (GlobalTheory.LogKSLoc.spMap_res_chart U W hW) hv

theorem comb_res : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (cf : Fin n → Γ(X, U.1)) (w : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left), IsCombAtG t (chart U) v cf w → IsCombAtG t (chart W) (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) (fun i => (X.presheaf.map (homOfLE hW).op).hom (cf i)) (spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ w) :=
  fun _ _ _ _ _ _ t U W hW _ _ _ _ h => comb_map t _ (GlobalTheory.LogKSLoc.spMap_res_chart U W hW) h

theorem agree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U, ∀ (f g : Γ(Y.X, U.1)) (DWf : Derivation ℤ Γ(Y.X, (Y.X.affineBasicOpen f).1) Γ(Y.X, (Y.X.affineBasicOpen f).1)) (DWg : Derivation ℤ Γ(Y.X, (Y.X.affineBasicOpen g).1) Γ(Y.X, (Y.X.affineBasicOpen g).1)), (∀ r, DWf ((Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le f)).op).hom r) = (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le f)).op).hom (D.1 r)) → (∀ r, DWg ((Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le g)).op).hom r) = (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le g)).op).hom (D.1 r)) → ∀ (Θf : Matrix (Fin n) (Fin n) Γ(Y.X, (Y.X.affineBasicOpen f).1)) (Θg : Matrix (Fin n) (Fin n) Γ(Y.X, (Y.X.affineBasicOpen g).1)), IsKS Y.t (interior Y) (Y.X.affineBasicOpen f) (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le f)).op).hom) ≫ v i) DWf Θf → IsKS Y.t (interior Y) (Y.X.affineBasicOpen g) (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le g)).op).hom) ≫ v i) DWg Θg → (Y.X.presheaf.map (homOfLE (inf_le_left : Y.X.basicOpen f ⊓ Y.X.basicOpen g ≤ Y.X.basicOpen f)).op).hom.mapMatrix Θf = (Y.X.presheaf.map (homOfLE (inf_le_right : Y.X.basicOpen f ⊓ Y.X.basicOpen g ≤ Y.X.basicOpen g)).op).hom.mapMatrix Θg := by
  intro E _ _ _ H Dw l Xo c Y h1 h2 h3 h4 U n v A hv hb hA D f g DWf DWg hDf hDg Θf Θg hKf hKg
  let P : Y.X.affineOpens := ⟨Y.X.basicOpen f ⊓ Y.X.basicOpen g, by
    rw [← Scheme.basicOpen_mul]; exact (Y.X.affineBasicOpen (f * g)).2⟩
  have hPU : P.1 ≤ U.1 := inf_le_left.trans (Y.X.basicOpen_le f)
  have hPf : P.1 ≤ (Y.X.affineBasicOpen f).1 := inf_le_left
  have hPg : P.1 ≤ (Y.X.affineBasicOpen g).1 := inf_le_right
  have hPf' : P.1 = Y.X.basicOpen ((Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le f)).op).hom g) :=
    (Scheme.basicOpen_res _ _ _).symm
  have hPg' : P.1 = Y.X.basicOpen ((Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le g)).op).hom f) := by
    rw [Scheme.basicOpen_res]; exact inf_comm _ _
  have hPUf : P.1 = Y.X.basicOpen (f * g) := (Scheme.basicOpen_mul _ _ _).symm
  obtain ⟨DP, hDPmem, hDP⟩ := GlobalTheory.LogDerLoc.exists_logDer_basicOpen Y.X _ Y.s _ U P hPU (f * g) hPUf D.1 D.2
  have cf := der_compat U f P.1 hPf hPU D.1 DWf DP hDf hDP
  have cg := der_compat U g P.1 hPg hPU D.1 DWg DP hDg hDP
  have kf := GlobalTheory.LogKSLoc.isKS_basicOpen E H Y.X Y.t (interior Y) _ P hPf _ hPf' n _ DWf DP Θf cf hKf
  have kg := GlobalTheory.LogKSLoc.isKS_basicOpen E H Y.X Y.t (interior Y) _ P hPg _ hPg' n _ DWg DP Θg cg hKg
  have fr : ∀ {V : Y.X.Opens} (hV : V ≤ U.1) (hPV : P.1 ≤ V) (i : Fin n),
      spMap (dualMap (Y.X.presheaf.map (homOfLE hPV).op).hom) ≫
        spMap (dualMap (Y.X.presheaf.map (homOfLE hV).op).hom) ≫ v i =
      spMap (dualMap (Y.X.presheaf.map (homOfLE hPU).op).hom) ≫ v i := by
    intro V hV hPV i
    rw [← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.dualMap_comp', res_comp]
  rw [show (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE hPf).op).hom) ≫
      spMap (dualMap (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le f)).op).hom) ≫ v i) =
      fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE hPU).op).hom) ≫ v i from funext (fr _ hPf)] at kf
  rw [show (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE hPg).op).hom) ≫
      spMap (dualMap (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le g)).op).hom) ≫ v i) =
      fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE hPU).op).hom) ≫ v i from funext (fr _ hPg)] at kg
  exact GlobalTheory.T.rigid_chart_dual_number_deformation E H Dw l Xo c Y h1 h2 h3 h4 P n _ (fun a => (Y.X.presheaf.map (homOfLE hPU).op).hom.mapMatrix (A a))
    (fun i => tan_res E H Y.X Y.t U P hPU _ (hv i))
    (fun w hw => by
      obtain ⟨cf, hcf⟩ := GlobalTheory.T.tangent_basis_extends_to_affine_open E H Y.X Y.t U P hPU (f * g) hPUf n v hv hb w hw
      exact ⟨cf, hcf, fun cf' h => GlobalTheory.T.tangent_coefficients_unique_affine_open E H Y.X Y.t U P hPU (f * g) hPUf n v hv hb cf' cf w h hcf⟩)
    (fun a i => by
      have := comb_res E H Y.X Y.t U P hPU n v (A a i) _ (hA a i)
      rw [Category.assoc]; exact this)
    ⟨DP, hDPmem⟩ _ _ kf kg

end GlobalTheory.KSAgree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBundleHodgeClass
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory.HodgeBig

theorem isBig_hodgeLine : Hypotheses2 → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p → 1 ≤ Dw.q → FnAlgClosed Xo c → ∀ (δ : LB (X₀ TF.Y Z)) (hδ : δ.IsLB), CechPic.pull (π₀ TF.X Z) (cls δ hδ) = cls (L₀ TF.X Z (hodgeWt Dw)) (isLB_L₀ TF.X Z _) → letI := algebraΓOfHom (s₀ TF.Y Z); IsBig c.F δ := by
  intro hP _ _ hS hK E _ _ _ H Dw l Xo c TF Z _ _ hF δ hδ hpull
  classical
  obtain ⟨ω, hω, e, hdom⟩ := HodgeDominates.exists_lb_dominates hP.p22 hS hK.toroidalChartsForFan TF
  obtain ⟨_, -, hproj, -, hsurj, -⟩ := GlobalTheory.BaseVar.isVariety_barComp E H Dw l Xo c TF Z hF
  have hprojY : IsProjOver (str₀ TF.X Z) := (GlobalTheory.VarFlag.isVariety₀_flag E H Dw l Xo c TF Z hF).2.1
  have hN := hP.q7
  let χ : AllWt.Weight Dw := fun _ i => if (i : ℕ) < Dw.p then (1 : ℤ) else -1
  have hB : (ω.pull (barComp TF.Y Z).ι).IsLB := pull_isLB hω _
  have hBp : CechPic.pull (π₀ TF.X Z) (cls _ hB) = cls (L₀ TF.X Z χ) (isLB_L₀ TF.X Z _) := by
    rw [cls_pull hω _ hB, ← CechPic.pull_comp, morphismRestrict_ι, CechPic.pull_comp, ← e]
    exact (cls_pull (TF.X.isLB_Llam _) _ _).symm
  let C := common₀ TF.X Z
  let φ := AddMonoidHom.mk' (fun a => cls (L₀ TF.X Z a) (C.isLB a)) (cls_common_add C)
  have hφ : ∀ a, cls (L₀ TF.X Z a) (isLB_L₀ TF.X Z a) = φ a := fun _ => rfl
  let w : AllWt.Weight Dw := ∑ τ : Psi H, NefWt.unitWt τ (-1)
  have ew : 2 • hodgeWt Dw - χ = w := by
    funext τ i
    simp only [w, Finset.sum_apply, NefWt.unitWt_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply,
      Pi.smul_apply, hodgeWt, CompHt.barWt, χ, smul_eq_mul]
    split_ifs <;> norm_num
  have hwnef : (letI := algebraΓOfHom (str₀ TF.X Z); IsNef c.F (L₀ TF.X Z w)) := by
    letI := algebraΓOfHom (str₀ TF.X Z)
    obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver hprojY
    refine IsNef.of_cls_eq_sum Finset.univ
      (fun τ : Psi H => (GlobalTheory.NefUnit.isNef_unitWt (GlobalTheory.CovTop.Hypotheses2.toClassicalTheorems hP) hN E H Dw l Xo c TF Z hF τ).2) (fun _ => 1) hA
      (isLB_L₀ TF.X Z w) ?_
    rw [hφ, map_sum]
    exact Finset.sum_congr rfl fun τ _ => (one_smul _ _).symm
  letI := algebraΓOfHom (s₀ TF.Y Z)
  have hf : ∀ r : c.F, algebraMap c.F Γ(X₀ TF.Y Z, ⊤) r =
      (s₀ TF.Y Z).appTop ((Scheme.ΓSpecIso (.of c.F)).inv r) := fun _ => rfl
  have hp' : IsProjOver (strHom c.F (X₀ TF.Y Z)) := by rw [strHom_eq hf]; exact hproj
  have h2 := isLB_lbPow hδ 2
  have hNl := LB.isLB_div h2 hB
  have hNp : CechPic.pull (π₀ TF.X Z) (cls _ hNl) = cls (L₀ TF.X Z w) (isLB_L₀ TF.X Z _) := by
    rw [cls_div h2 hB hNl, map_sub, cls_lbPow hδ 2 h2, map_nsmul, hpull, hBp, hφ, hφ, hφ, ← ew, map_sub, map_nsmul]
  have hNnef : IsNef c.F (LB.div (lbPow δ 2) (ω.pull (barComp TF.Y Z).ι)) :=
    GlobalTheory.NefDescent.isNef_of_pull c.F _ _ (π₀ TF.X Z) (s₀ TF.Y Z) (str₀ TF.X Z) _ hNl _
      (isLB_L₀ TF.X Z w) (π₀_s₀ TF.X Z) hproj hprojY hsurj hNp hwnef
  have : IsProper (s₀ TF.Y Z) := ThetaDescent.isProper_of_isProjOver hproj
  have : CompactSpace (X₀ TF.Y Z) := QuasiCompact.compactSpace_of_compactSpace (s₀ TF.Y Z)
  obtain ⟨A, hA⟩ := exists_isAmpleLB_of_isProjOver TF.Y.proj
  have hA₀ : IsAmpleLB (A.pull (barComp TF.Y Z).ι) := hA.pull_of_isOpenImmersion _
  have hw : TF.Y.j (genPt Z) ∈ barComp TF.Y Z := (j_mem_barComp Z _).2 (CompSplitPfB.cspB_genPt_mem Z)
  obtain ⟨m, hm, s, hs⟩ := hdom (genPt Z) A hA.isLB
  have hD := LB.isLB_div (isLB_lbPow hω m) hA.isLB
  have ht : (⟨_, hw⟩ : X₀ TF.Y Z) ∈ nonzeroLocus (lbSecPull _ s (barComp TF.Y Z).ι) := by
    rw [HodgeDominates.nonzeroLocus_lbSecPull]
    exact hs
  have hNm := hNnef.pow hA₀ m
  have hbig := hNm.isBig_tens_ample hN hp' hA₀
  have hδm : IsBig c.F (lbPow δ (2 * m)) :=
    hbig.of_cls_eq_add hf hproj (pull_isLB hD _) ⟨_, sec_ne_zero_of_mem ht⟩ (isLB_lbPow hδ _) (by
      rw [cls_tens hNm.isLB hA₀.isLB, cls_lbPow hNl, cls_div h2 hB hNl, cls_lbPow hδ, cls_lbPow hδ, cls_pull hω,
        cls_pull hA.isLB, cls_pull hD, cls_div (isLB_lbPow hω m) hA.isLB, cls_lbPow hω, map_sub, map_nsmul,
        smul_sub, mul_comm, mul_smul]
      abel)
  exact hδm.of_pow hδ (by omega) fun n => finite_coh_zero_twist_of_isProjOver hf hproj (isLB_lbPow hδ n)

end GlobalTheory.HodgeBig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalRestrictionRelAmpleLocusOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.FibreAmple

noncomputable section

namespace GlobalTheory.DiagAmpleLocus

theorem diag_relAmple_locus : ∀ (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (A' : Over T) [GrpObj A'] (φ : A'.left ⟶ G.left) (φ₂ : (G2 A').left ⟶ (G2 G).left) (P' : LB (G2 A').left), IsGrpPullback A' G g φ → IsSquare φ φ₂ → P'.IsLB → LBIso P' (P.pull φ₂) → Out.RelAmple A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) → Set.range g.base ⊆ (U : Set S') := by
  intro S' _ G _ _ P hG hP
  have := hG.proper
  have : Flat G.hom := by have := hG.smooth; infer_instance
  have hD : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  let good : Set S' := {s | ∃ (Y X : Scheme.{0}) (j : Y ⟶ S') (_ : IsOpenImmersion j) (π : X ⟶ G.left)
      (f : X ⟶ Y), IsPullback π f G.hom j ∧ s ∈ Set.range j.base ∧
        RelAmple (Over.mk f) ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull π)}
  have hopen : IsOpen good := by
    rw [isOpen_iff_forall_mem_open]
    rintro s ⟨Y, X, j, hj, π, f, h, hs, hA⟩
    exact ⟨Set.range j.base, fun x hx => ⟨Y, X, j, hj, π, f, h, hx, hA⟩,
      j.isOpenEmbedding.isOpen_range, hs⟩
  refine ⟨⟨good, hopen⟩, fun V hV => ?_, ?_⟩
  · let AV := (Over.pullback V.ι).obj G
    have : IsProper AV.hom := inferInstanceAs (IsProper (pullback.snd G.hom V.ι))
    have key : RelAmple AV ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull (pullback.fst G.hom V.ι)) := by
      refine GlobalTheory.AmpleLocal.relAmple_of_locally V AV _ (pull_isLB hD _) inferInstance inferInstance
        fun v => ?_
      obtain ⟨Y, X, j, hj, π, f, h, ⟨y, hy⟩, hA⟩ := hV v.2
      let V' : V.toScheme.Opens := V.ι ⁻¹ᵁ j.opensRange
      have hv : v ∈ V' := ⟨y, hy⟩
      have hrange : Set.range (V'.ι ≫ V.ι).base ⊆ Set.range j.base := by
        rintro _ ⟨w, rfl⟩
        exact w.2
      have sq : IsPullback ((AV.hom ⁻¹ᵁ V').ι ≫ pullback.fst G.hom V.ι) (AV.hom ∣_ V') G.hom (V'.ι ≫ V.ι) :=
        (isPullback_morphismRestrict AV.hom V').flip.paste_horiz (IsPullback.of_hasPullback G.hom V.ι)
      have h₁ := relAmple_of_factor hD h sq (IsOpenImmersion.lift j _ hrange)
        (IsOpenImmersion.lift_fac _ _ _) (pull_isLB hD π) (GlobalTheory.lbIso_refl (pull_isLB hD π)) hA
      have : IsProper (Over.mk (AV.hom ∣_ V')).hom := inferInstanceAs (IsProper (AV.hom ∣_ V'))
      exact ⟨V', hv, GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hD _)
        (pull_isLB (pull_isLB hD _) _) (lbIso_pull_pull hD _ _) h₁⟩
    have e₁ : LBIso ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 AV) (𝟙 AV)).left)
        (P.pull ((lift (𝟙 AV) (𝟙 AV)).left ≫ Pdiv.PullbackComparison.pφ₂ V.ι G)) :=
      GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
    rw [GlobalTheory.DiagAmpleBC.diag_comp G AV _ _ (Pdiv.PullbackComparison.isSquare V.ι G)] at e₁
    have e₂ : LBIso ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull (Pdiv.PullbackComparison.pφ V.ι G))
        (P.pull (Pdiv.PullbackComparison.pφ V.ι G ≫ (lift (𝟙 G) (𝟙 G)).left)) :=
      GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
    exact GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hD _) (pull_isLB (pull_isLB hP _) _)
      (LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB hD _) e₁ e₂.symm) key
  · rintro T g A' _ φ φ₂ P' hpb hsq hP' e hA _ ⟨t, rfl⟩
    have h₀ : IsPullback φ A'.hom G.hom g := hpb.1
    have : IsProper A'.hom := MorphismProperty.of_isPullback (P := @IsProper) h₀ ‹_›
    have e₁ : LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) (P.pull ((lift (𝟙 A') (𝟙 A')).left ≫ φ₂)) :=
      GlobalTheory.ZM.SiegPull.lbIso_pull_comp e _
    rw [GlobalTheory.DiagAmpleBC.diag_comp G A' φ φ₂ hsq] at e₁
    have e₂ : LBIso ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull φ) (P.pull (φ ≫ (lift (𝟙 G) (𝟙 G)).left)) :=
      GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.lbIso_refl (pull_isLB hP _)) _
    have hA' : RelAmple A' ((P.pull (lift (𝟙 G) (𝟙 G)).left).pull φ) :=
      GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hP' _) (pull_isLB hD _)
        (LBIso.trans (pull_isLB hD _) (pull_isLB hP _) (pull_isLB hP' _) e₂ e₁.symm) hA
    obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S') (U := ⊤) (x := g.base t) trivial
    have : IsNoetherianRing Γ(S', V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
    obtain ⟨VT, hVT, ht, hle⟩ := exists_isAffineOpen_mem_and_subset (X := T) (U := g ⁻¹ᵁ V) (x := t) hs
    obtain ⟨q, hq⟩ : t ∈ Set.range hVT.fromSpec.base := by rw [hVT.range_fromSpec]; exact ht
    let tV : Sp Γ(S', V) ⟶ S' := hV.fromSpec
    let φR := g.appLE V VT hle
    have sqR : Spec.map φR ≫ hV.fromSpec = hVT.fromSpec ≫ g := IsAffineOpen.SpecMap_appLE_fromSpec g hV hVT hle
    let p : PrimeSpectrum Γ(S', V) := (Spec.map φR).base q
    have hp : tV.base p = g.base t := by
      have := congrArg (fun f : Spec Γ(T, VT) ⟶ S' => f.base q) sqR
      simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at this
      rw [← hq]
      exact this
    have : q.asIdeal.IsPrime := PrimeSpectrum.isPrime (q : PrimeSpectrum Γ(T, VT))
    have : p.asIdeal.IsPrime := PrimeSpectrum.isPrime p
    let k := p.asIdeal.ResidueField
    let kq := q.asIdeal.ResidueField
    let gR := algebraMap Γ(S', V) k
    let i : k →+* kq := Ideal.ResidueField.map p.asIdeal q.asIdeal φR.hom rfl
    have hi : spMap (algebraMap Γ(T, VT) kq) ≫ Spec.map φR = spMap i ≫ spMap gR := by
      show Spec.map (CommRingCat.ofHom _) ≫ Spec.map φR = Spec.map (CommRingCat.ofHom i) ≫ Spec.map (CommRingCat.ofHom gR)
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext x
      exact (Ideal.ResidueField.map_algebraMap _ _ _ _ x).symm
    let y : Sp kq ⟶ S' := spMap i ≫ spMap gR ≫ tV
    have hu : (spMap (algebraMap Γ(T, VT) kq) ≫ hVT.fromSpec) ≫ g = y := by
      rw [Category.assoc, ← sqR, ← Category.assoc, hi, Category.assoc]
    have hfib := relAmple_of_factor hD h₀ (IsPullback.of_hasPullback G.hom y) _ hu (pull_isLB hD φ)
      (GlobalTheory.lbIso_refl (pull_isLB hD φ)) hA'
    let B : Over (Sp Γ(S', V)) := Over.mk (pullback.snd G.hom tV)
    have : IsProper B.hom := inferInstanceAs (IsProper (pullback.snd G.hom tV))
    have : Flat B.hom := inferInstanceAs (Flat (pullback.snd G.hom tV))
    have hB := IsPullback.of_hasPullback G.hom tV
    have hL := pull_isLB hD (pullback.fst G.hom tV)
    obtain ⟨r, hr, hAr⟩ := GlobalTheory.ProperFinite.relAmple_near_fibre B hL gR (residueField_fraction p.asIdeal)
      (relAmple_of_fieldExtension hD i ((IsPullback.of_hasPullback B.hom (spMap gR)).paste_horiz hB)
        (IsPullback.of_hasPullback G.hom _) (pull_isLB hL _) (lbIso_pull_pull hD _ _) hfib)
    let Dr : (Sp Γ(S', V)).Opens := PrimeSpectrum.basicOpen r
    have hpD : p ∈ Dr := fun h => hr (Ideal.algebraMap_residueField_eq_zero.2 h)
    have : IsProper (Over.mk (pullback.snd B.hom Dr.ι)).hom := inferInstanceAs (IsProper (pullback.snd B.hom Dr.ι))
    exact ⟨Dr.toScheme, _, Dr.ι ≫ tV, inferInstance, pullback.fst B.hom Dr.ι ≫ pullback.fst G.hom tV,
      pullback.snd B.hom Dr.ι, (IsPullback.of_hasPullback B.hom Dr.ι).paste_horiz hB, ⟨⟨p, hpD⟩, hp⟩,
      GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB hL _) (pull_isLB hD _) (lbIso_pull_pull hD _ _).symm hAr⟩

end GlobalTheory.DiagAmpleLocus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianPartFunctionOfWeightUnitLogDeriv
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
open GlobalTheory.HeatConn
open GlobalTheory.HeatConn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn.LogDerDesc

theorem exists_app_mul_eq_dE : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) (ν : R), (∀ a (α : Q.X) (V : Y.H.left.Opens) f, IsWt Y α V f → IsWt Y α V (dd a V f)) → IsBasic Y h → ∀ (i : h.J) (α : Q.X) (U : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ U ≤ h.W i → ∀ x : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U), IsUnit x → IsWt Y α _ x → ∃ A : Γ(Q.P.A.left, U), (Y.q.left.app U).hom A * x = dE h ν i _ x := by
  intro R _ _ Q O _ _ _ oa Y n dd D h ν hdd hB i α U hU x hx hxw

  have h1 : IsWt Y α _ (dE h ν i _ x) := by
    unfold dE
    refine WtAlg.isWt_add ((hB i).2.2.2 α U hU x hxw) (WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ _) ?_)
    exact WtAlg.isWt_sum _ _ fun a _ => WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (WtAlg.isWt_constFn _ _) (hdd a α _ x hxw)

  have h2 : IsWt Y 0 _ (dE h ν i _ x * ((hx.unit⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U)ˣ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U))) := by
    intro S _ φ y y' c a a' ha ha' hV hV' hq hc
    have one : ∀ (b : Sp S ⟶ Y.H.left) (hb : ⊤ ≤ b ⁻¹ᵁ (Y.q.left ⁻¹ᵁ U)),
        valR b _ x * valR b _ ((hx.unit⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U)ˣ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U)) = 1 := by
      intro b hb
      rw [← WtAlg.valR_mul'' _ _ hb, IsUnit.mul_val_inv, WtAlg.valR_eq' _ _ hb, map_one, map_one]
    have e1 := h1 S φ y y' c a a' ha ha' hV hV' hq hc
    have ex := hxw S φ y y' c a a' ha ha' hV hV' hq hc
    have o := one a hV
    have o' := one a' hV'
    rw [WtAlg.valR_mul'' _ _ hV', WtAlg.valR_mul'' _ _ hV, e1, WtAlg.c_zero y y' c hc, Units.val_one, _root_.one_mul]
    rw [ex] at o'
    linear_combination (-((c α : S)) * valR a _ (dE h ν i _ x) * valR a' _ ((hx.unit⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U)ˣ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U))) * o
      + (valR a _ (dE h ν i _ x) * valR a _ ((hx.unit⁻¹ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U)ˣ) : Γ(Y.H.left, Y.q.left ⁻¹ᵁ U))) * o'

  obtain ⟨A, hA⟩ := AbConst.exists_app_eq Y h2
  refine ⟨A, ?_⟩
  rw [hA, _root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]

end GlobalTheory.HeatConn.LogDerDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithHeightEqMixedHeightDiagonalStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arithHeight_eq_mixedHeight_diagonal : ArchInteg → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ T, IsMix p (D + 1) T → ∀ N : HermLB p, ∃ h : X → ℝ, N.IsArithHeight h ∧ ∀ (x : X) (d : ℕ), HasDim x d → h x = T d (fun _ => N) x := by
  first | exact @GlobalTheory.MixHtDiag.exists_isArithHeight | exact GlobalTheory.MixHtDiag.exists_isArithHeight | (intros; apply GlobalTheory.MixHtDiag.exists_isArithHeight <;> assumption)
end

