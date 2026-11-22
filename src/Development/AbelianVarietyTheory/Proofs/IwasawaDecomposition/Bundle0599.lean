import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0491
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0584
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0583
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPullbackOfNormalFlatProj
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryStabilizerScalingIsotropic
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem hypRot_smul_mem (X : Data E N) {s : E} (hs : IsIntegral ℤ s) {v : Fin N → E}
    (hv : v ∈ X.Λ) : s • v ∈ X.Λ := by
  have : s • v = (⟨s, hs⟩ : 𝓞 E) • v := by
    rw [← algebraMap_smul E (⟨s, hs⟩ : 𝓞 E) v]; rfl
  rw [this]; exact X.Λ.smul_mem _ hv

theorem hypRot_mulVec (X : Data E N) (ξ η : Fin N → E) (a b : E) (x : Fin N → E) :
    (1 + a • rk1 X.Gm ξ η + b • rk1 X.Gm η ξ).mulVec x =
      x + (a * herm X.Gm x η) • ξ + (b * herm X.Gm x ξ) • η := by
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, one_add_smul_vecMulVec_mulVec, smul_smul]

theorem hypRot_mul_hypRot (X : Data E N) (ξ η : Fin N → E) (d : ℕ) (a b : E)
    (hξξ : herm X.Gm ξ ξ = 0) (hηη : herm X.Gm η η = 0) (hξη : herm X.Gm ξ η = d)
    (hηξ : herm X.Gm η ξ = d) (key : a + b + a * b * d = 0) :
    (1 + a • rk1 X.Gm ξ η + b • rk1 X.Gm η ξ) * (1 + b • rk1 X.Gm ξ η + a • rk1 X.Gm η ξ) = 1 := by
  have hPP : rk1 X.Gm ξ η * rk1 X.Gm ξ η = (d : E) • rk1 X.Gm ξ η := by rw [one_add_smul_vecMulVec_mul, hξη]
  have hPQ : rk1 X.Gm ξ η * rk1 X.Gm η ξ = 0 := by rw [one_add_smul_vecMulVec_mul, hηη, zero_smul]
  have hQP : rk1 X.Gm η ξ * rk1 X.Gm ξ η = 0 := by rw [one_add_smul_vecMulVec_mul, hξξ, zero_smul]
  have hQQ : rk1 X.Gm η ξ * rk1 X.Gm η ξ = (d : E) • rk1 X.Gm η ξ := by rw [one_add_smul_vecMulVec_mul, hηξ]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hPP, hPQ, hQP, hQQ,
    smul_zero, smul_smul]
  calc _ = 1 + (a + b + a * b * d) • rk1 X.Gm ξ η + (a + b + a * b * d) • rk1 X.Gm η ξ := by module
    _ = 1 := by rw [key, zero_smul, zero_smul, add_zero, add_zero]

theorem herm_hypRot (X : Data E N) (ξ η : Fin N → E) (d : ℕ) (a b : E)
    (hξξ : herm X.Gm ξ ξ = 0) (hηη : herm X.Gm η η = 0) (hξη : herm X.Gm ξ η = d)
    (hηξ : herm X.Gm η ξ = d) (ha : cc a = a) (hb : cc b = b) (key : a + b + a * b * d = 0)
    (x y : Fin N → E) :
    herm X.Gm (x + (a * herm X.Gm x η) • ξ + (b * herm X.Gm x ξ) • η)
      (y + (a * herm X.Gm y η) • ξ + (b * herm X.Gm y ξ) • η) = herm X.Gm x y := by
  have hc := cc_herm X.Gm X.Gm_herm
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, cc_mul, ha, hb, hc,
    hξξ, hηη, hξη, hηξ]
  linear_combination (herm X.Gm x ξ * herm X.Gm η y + herm X.Gm x η * herm X.Gm ξ y) * key

theorem exists_isUStab_hypRot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (ξ η : Fin N → E) (d : ℕ) (ε : E) (c : 𝓞 E), 0 < d → ξ ∈ X.Λ → η ∈ X.Λ → herm X.Gm ξ ξ = 0 → herm X.Gm η η = 0 → herm X.Gm ξ η = d → cc ε = ε → ε ≠ 0 → IsIntegral ℤ ε → IsIntegral ℤ ε⁻¹ → ε - 1 = d * X.den * c → ∃ g : GL (Fin N) E, IsUStab X.Gm X.Λ g ∧ (g : Matrix (Fin N) (Fin N) E).mulVec ξ = ε • ξ := by
  intro E _ _ _ N X ξ η d ε c hd hξ hη hξξ hηη hξη hεr hε0 hεi hεii hεc
  have hdE : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  have hηξ : herm X.Gm η ξ = d := by rw [← cc_herm X.Gm X.Gm_herm ξ η, hξη, cc_natCast]
  obtain ⟨a, ha_def⟩ : ∃ a : E, a = (ε - 1) / d := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : E, b = (ε⁻¹ - 1) / d := ⟨_, rfl⟩
  have ha : cc a = a := by
    rw [ha_def, div_eq_mul_inv, cc_mul, cc_inv, cc_sub, cc_one, cc_natCast, hεr]
  have hb : cc b = b := by
    rw [hb_def, div_eq_mul_inv, cc_mul, cc_inv, cc_sub, cc_one, cc_natCast, cc_inv, hεr]
  have key : a + b + a * b * d = 0 := by
    rw [ha_def, hb_def]; field_simp; ring
  have key' : b + a + b * a * d = 0 := by linear_combination key
  have ha' : a = (X.den : E) * c := by
    rw [ha_def, div_eq_iff hdE, hεc]; ring
  have hinv : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε0
  have hb' : b = -(ε⁻¹ * ((X.den : E) * c)) := by
    rw [hb_def, div_eq_iff hdE]; linear_combination (-ε⁻¹) * hεc + hinv
  have hA : ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, IsIntegral ℤ (a * herm X.Gm x y) := by
    intro x hx y hy
    rw [ha', show (X.den : E) * c * herm X.Gm x y = c * (X.den * herm X.Gm x y) by ring]
    exact (RingOfIntegers.isIntegral_coe c).mul (X.Λ_int x hx y hy)
  have hB : ∀ x ∈ X.Λ, ∀ y ∈ X.Λ, IsIntegral ℤ (b * herm X.Gm x y) := by
    intro x hx y hy
    rw [hb', show -(ε⁻¹ * ((X.den : E) * c)) * herm X.Gm x y =
      -(ε⁻¹ * c * (X.den * herm X.Gm x y)) by ring]
    exact ((hεii.mul (RingOfIntegers.isIntegral_coe c)).mul (X.Λ_int x hx y hy)).neg
  have h01 := hypRot_mul_hypRot X ξ η d a b hξξ hηη hξη hηξ key
  have h10 := hypRot_mul_hypRot X ξ η d b a hξξ hηη hξη hηξ key'
  have hm0 : ∀ x ∈ X.Λ, (1 + a • rk1 X.Gm ξ η + b • rk1 X.Gm η ξ).mulVec x ∈ X.Λ := by
    intro x hx
    rw [hypRot_mulVec]
    exact X.Λ.add_mem (X.Λ.add_mem hx (hypRot_smul_mem X (hA x hx η hη) hξ))
      (hypRot_smul_mem X (hB x hx ξ hξ) hη)
  have hm1 : ∀ x ∈ X.Λ, (1 + b • rk1 X.Gm ξ η + a • rk1 X.Gm η ξ).mulVec x ∈ X.Λ := by
    intro x hx
    rw [hypRot_mulVec]
    exact X.Λ.add_mem (X.Λ.add_mem hx (hypRot_smul_mem X (hB x hx η hη) hξ))
      (hypRot_smul_mem X (hA x hx ξ hξ) hη)
  refine ⟨⟨_, _, h01, h10⟩, ⟨fun x y => ?_, fun x => ⟨hm0 x, fun h => ?_⟩⟩, ?_⟩
  · show herm X.Gm ((1 + a • rk1 X.Gm ξ η + b • rk1 X.Gm η ξ).mulVec x)
      ((1 + a • rk1 X.Gm ξ η + b • rk1 X.Gm η ξ).mulVec y) = herm X.Gm x y
    rw [hypRot_mulVec, hypRot_mulVec]
    exact herm_hypRot X ξ η d a b hξξ hηη hξη hηξ ha hb key x y
  · have := hm1 _ h
    rwa [Matrix.mulVec_mulVec, h10, Matrix.one_mulVec] at this
  · show (1 + a • rk1 X.Gm ξ η + b • rk1 X.Gm η ξ).mulVec ξ = ε • ξ
    rw [hypRot_mulVec, hξη, hξξ, mul_zero, zero_smul, add_zero]
    have : a * d = ε - 1 := by rw [ha_def]; field_simp
    rw [this]; module

end GlobalTheory.UnipKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietiesComponentsSmoothGenericFibre
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.GenFibreComp

theorem exists_fn_hom {F L : Type} [Field F] [Field L] {V : Scheme.{0}} [IsIntegral V] (p : V ⟶ Sp F)
    (g : Sp L ⟶ V) (hg : g (IsLocalRing.closedPoint L) = genericPoint V) (ψ : F →+* L) (hψ : g ≫ p = spMap ψ) :
    ∃ φ : V.functionField →+* L, φ.comp (GlobalTheory.Cartier.constFn p) = ψ := by
  have hs : g (IsLocalRing.closedPoint L) ⤳ genericPoint V := hg ▸ specializes_rfl
  refine ⟨(V.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo g).hom, ?_⟩
  have h1 : V.presheaf.germ ⊤ (genericPoint V) (TopologicalSpace.Opens.mem_top _) ≫ V.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo g
      = g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom := by
    rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.germ_stalkClosedPointTo]
    exact congrArg (g.app ⊤ ≫ ·) ((congrArg (· ≫ _) ((Spec (CommRingCat.of L)).presheaf.map_id _)).trans
      (Category.id_comp _))
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ p.appTop ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom
      = CommRingCat.ofHom ψ := by
    rw [← Scheme.Hom.comp_appTop_assoc, hψ, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rw [← h1] at h2
  ext a
  have h3 := congrArg (fun t => t.hom a) h2
  refine Eq.trans ?_ h3
  have h4 : p.appLE ⊤ ⊤ le_top = p.appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact (congrArg (p.app ⊤ ≫ ·) (V.presheaf.map_id _)).trans (Category.comp_id _)
  rw [← h4]
  rfl

theorem isProjOver_comp_equiv {F K : Type} [Field F] [Field K] (e : F ≃+* K) {X : Scheme.{0}} (p : X ⟶ Sp K)
    (h : IsProjOver p) : IsProjOver (p ≫ spMap e.toRingHom) := by
  have hi : spMap e.symm.toRingHom ≫ spMap e.toRingHom = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; simp
  have hi' : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; simp
  have : IsIso (spMap e.symm.toRingHom) := ⟨_, hi, hi'⟩
  have h1 := (GlobalTheory.ProjSpace.points_and_stability K 0).2.2.1 F e.symm.toRingHom X p h
  have h2 := (GlobalTheory.ProjSpace.points_and_stability F 0).2.2.2.1 _ _ (inv (pullback.fst p (spMap e.symm.toRingHom))) _
    inferInstance h1
  convert h2 using 1
  rw [IsIso.eq_inv_comp, pullback.condition_assoc, hi, Category.comp_id]

theorem exists_vars : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F), FnAlgClosed Xo c → SmoothOfRelativeDimension Dw.dim (genStr Z) → ∃ (B : Comp Xo c → GlobalTheory.ProjVar.Var F) (j : ∀ i, (B i).X ⟶ gen Z), (∀ i, IsOpenImmersion (j i) ∧ (B i).dim = Dw.dim ∧ j i ≫ genStr Z ≫ spMap e.toRingHom = (B i).str ∧ ∀ p ∈ i.1, Z.jQ p ∈ Set.range (j i)) ∧ ∀ z : gen Z, ∃! i, z ∈ Set.range (j i) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e hF hsm
  have hS : Smooth (genStr Z) := SmoothOfRelativeDimension.smooth Dw.dim _
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  have : CompactSpace (gen Z) := QuasiCompact.compactSpace_of_compactSpace (genStr Z)
  have : IsNoetherian (gen Z) := {}
  have := Z.jQ_open
  have hcc := fun z : gen Z => PtComp.connectedComponent_mem
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (fun W hW W' hW' => PtComp.disjoint_of_smooth (genStr Z) hS W W' hW hW') z
  have hgen : ∀ i : Comp Xo c, IsGenericPoint (genPt i) i.1 := fun i => CompSplitPfD.cspD_gen i.2
  have hpre : ∀ i : Comp Xo c, Z.jQ ⁻¹' connectedComponent (Z.jQ (genPt i)) = i.1 := fun i => by
    by_contra hn
    exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _
      ⟨_, PtComp.preimage_connectedComponent_mem Z hS (Z.jQ (genPt i))⟩ i fun h => hn (congrArg Subtype.val h))
      mem_connectedComponent (hgen i).mem
  let V : Comp Xo c → (gen Z).Opens := fun i => ⟨connectedComponent (Z.jQ (genPt i)), (hcc _).2⟩
  have hred : IsReduced (gen Z) := by
    have := GlobalTheory.isNormalScheme_of_smooth (genStr Z)
    exact GlobalTheory.IsNormalScheme.isReduced
  have : CharZero F := e.toRingHom.charZero
  have : IsIso (spMap e.toRingHom) :=
    inferInstanceAs (IsIso (Spec.map e.toCommRingCatIso.hom))
  have hproj : IsProjOver (genStr Z ≫ spMap e.toRingHom) := isProjOver_comp_equiv e _
    ((GlobalTheory.ProjSpace.points_and_stability O 0).2.2.1 c.F β Z.X Z.s Z.proj)
  have key : ∀ i, ∃ (Y : GlobalTheory.ProjVar.Var F) (ε : (V i).toScheme ≅ Y.X), Y.dim = Dw.dim ∧
      ε.hom ≫ Y.str = (V i).ι ≫ genStr Z ≫ spMap e.toRingHom := fun i => by
    have : IrreducibleSpace (V i).toScheme := Subtype.irreducibleSpace (hcc _).1.1
    have : IsIntegral (V i).toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
    have hcl : IsClosedImmersion (V i).ι := IsClosedImmersion.of_isPreimmersion _ (by
      rw [Scheme.Opens.range_ι]; exact isClosed_connectedComponent)
    have hp : IsProjOver ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) :=
      (GlobalTheory.ProjSpace.points_and_stability F 0).2.2.2.1 _ _ _ _ hcl hproj
    have hsd : SmoothOfRelativeDimension Dw.dim ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) := by
      have h : SmoothOfRelativeDimension (0 + (Dw.dim + 0)) ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) := inferInstance
      simpa using h
    have hr : Set.range (genSp i ≫ Z.jQ) ⊆ Set.range (V i).ι := by
      rintro _ ⟨s, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply, genSp, Scheme.fromSpecResidueField_apply]
      exact mem_connectedComponent
    let g : Sp (kap i) ⟶ (V i).toScheme := IsOpenImmersion.lift (V i).ι (genSp i ≫ Z.jQ) hr
    have hg : g ≫ (V i).ι = genSp i ≫ Z.jQ := IsOpenImmersion.lift_fac _ _ _
    have hgp : (V i).ι (g (IsLocalRing.closedPoint (kap i))) = Z.jQ (genPt i) := by
      exact (Scheme.Hom.comp_apply g (V i).ι _).symm.trans ((congrArg (fun t : Sp (kap i) ⟶ gen Z => t (IsLocalRing.closedPoint (kap i))) hg).trans
        ((Scheme.Hom.comp_apply _ _ _).trans (congrArg Z.jQ (Scheme.fromSpecResidueField_apply _ _))))
    have hgg : g (IsLocalRing.closedPoint (kap i)) = genericPoint (V i).toScheme := by
      have h1 : (V i).ι (genericPoint (V i).toScheme) ⤳ Z.jQ (genPt i) :=
        hgp ▸ (genericPoint_specializes _).map (V i).ι.continuous
      obtain ⟨a, ha⟩ := h1.mem_open Z.jQ.isOpenEmbedding.isOpen_range ⟨_, rfl⟩
      have h2 : a = genPt i := CompSplitPfD.cspD_max i.2 (hgen i) a
        (Z.jQ.isOpenEmbedding.isInducing.specializes_iff.1 (ha ▸ h1))
      apply (V i).ι.isOpenEmbedding.injective
      rw [hgp, ← ha, h2]
    obtain ⟨φ, hφ⟩ := exists_fn_hom ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) g hgg
      ((algebraMap c.F (kap i)).comp e.toRingHom) (by
        rw [reassoc_of% hg, reassoc_of% Z.jQ_over, ← Category.assoc]
        exact (congrArg (· ≫ _) (Spec.map_preimage (genSp i ≫ strK)).symm).trans (Spec.map_comp _ _).symm)
    have : GeometricallyConnected ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom) := by
      refine GlobalTheory.GeomConnFn.geometricallyConnected_of_locallyOfFiniteType _ ?_
      rintro a ⟨P, hP, hPa⟩
      let χ : (V i).toScheme.functionField →+* Om i := (algebraMap (kap i) (Om i)).comp φ
      have hχ : χ.comp (GlobalTheory.Cartier.constFn ((V i).ι ≫ genStr Z ≫ spMap e.toRingHom)) =
          (algebraMap c.F (Om i)).comp e.toRingHom := by
        rw [RingHom.comp_assoc, hφ, IsScalarTower.algebraMap_eq c.F (kap i) (Om i), RingHom.comp_assoc]
      obtain ⟨b, hb⟩ := hF i (χ a) ⟨P.map e.toRingHom, (Polynomial.map_ne_zero_iff e.injective).2 hP, by
        rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hχ, ← Polynomial.hom_eval₂, hPa, map_zero]⟩
      refine ⟨e.symm b, χ.injective ?_⟩
      rw [← hb]
      exact (RingHom.congr_fun hχ _).trans (by simp)
    exact GlobalTheory.ProjVar.Var.exists_iso _ Dw.dim hp
  choose B ε hd hs using key
  have hrange : ∀ i, Set.range ((ε i).inv ≫ (V i).ι) = connectedComponent (Z.jQ (genPt i)) := fun i => by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, (ε i).inv.surjective.range_eq, Set.image_univ,
      Scheme.Opens.range_ι]
    rfl
  refine ⟨B, fun i => (ε i).inv ≫ (V i).ι, fun i => ⟨inferInstance, hd i, ?_, fun p hp => ?_⟩, fun z => ?_⟩
  · rw [Category.assoc, ← hs, Iso.inv_hom_id_assoc]
  · rw [hrange]
    rw [← hpre] at hp
    exact hp
  · refine ⟨⟨_, PtComp.preimage_connectedComponent_mem Z hS z⟩, ?_, fun i hi => ?_⟩
    · beta_reduce
      rw [hrange]
      have h := (hgen ⟨_, PtComp.preimage_connectedComponent_mem Z hS z⟩).mem
      rw [← connectedComponent_eq (show Z.jQ _ ∈ connectedComponent z from h)]
      exact mem_connectedComponent
    · beta_reduce at hi
      rw [hrange] at hi
      apply Subtype.ext
      rw [← hpre, connectedComponent_eq hi]

end GlobalTheory.GenFibreComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameCombinationCoeffUnique
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj

namespace GlobalTheory.Proof.frame_combination_coeff_unique

attribute [local instance] Over.cartesianMonoidalCategory

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem pairwise_letters (Dw : Datum H) :
    (letters Dw).Pairwise fun x y : GlobalTheory.ShFam.Pad.Letter Dw => x.1 = y.1 → (x.2 : ℕ) < y.2 := by
  refine List.pairwise_flatMap.2 ⟨fun a _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    refine (List.pairwise_lt_finRange _).imp ?_
    exact fun h _ => h
  · refine (List.nodup_finRange _).pairwise_of_forall_ne fun a _ b _ hab => ?_
    intro x hx y hy h
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i', -, rfl⟩ := List.mem_map.1 hy
    exact absurd ((Fintype.equivFin (E →+* ℂ)).symm.injective h) hab

theorem get_bijective (Dw : Datum H) : Function.Bijective (letters Dw).get :=
  ⟨List.nodup_iff_injective_get.1 (LetterConjugation.nodup_letters Dw), fun x => List.get_of_mem (LetterConjugation.mem_letters Dw x)⟩

variable {X : Scheme.{0}} {t : SAB H X} {k : Type} [CommRing k] {x : Sp k ⟶ X}

theorem comb_iff {m : ℕ} (u : Fin m → TanM x t.G) (a : Fin m → k) (w : Sp (DualNumber k) ⟶ t.G.left) :
    IsCombAtG t x (fun i => (tv (u i)).left) a w ↔ w = (tv (∑ i, a i • u i)).left := by
  have h0 := (GlobalTheory.LieMet.isComb_iff u a _).2 rfl
  refine ⟨fun h => ?_, fun h => h ▸ h0⟩
  obtain ⟨p, hp, rfl⟩ := h
  obtain ⟨q, hq, hq'⟩ := h0
  obtain rfl : p = q := funext fun i => Over.OverMorphism.ext ((hp i).trans (hq i).symm)
  exact hq'

end

theorem concat_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (k : Type) [Field k] (f : c.F →+* k) (x : Sp k ⟶ X) (u : Vecs Dw t k), GlobalTheory.LocM.IsFrame t f x u → (∀ cf cf' w, IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cf w → IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cf' w → cf = cf') ∧ ∀ (j : Fin (letters Dw).length) (cf : Fin (Dw.mult ((letters Dw).get j).1) → k) w, (∀ m, ((letters Dw).get j).2 < m → cf m = 0) → IsCombAtG t x (u ((letters Dw).get j).1) cf w → ∃ cg : Fin (letters Dw).length → k, (∀ m, j < m → cg m = 0) ∧ cg j = cf ((letters Dw).get j).2 ∧ IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2) cg w := by
  intro E _ _ _ H Dw l c X t k _ f x u hu
  classical
  let _ : Algebra c.F k := f.toAlgebra
  let U : (y : GlobalTheory.ShFam.Pad.Letter Dw) → TanM x t.G := fun y => GlobalTheory.LieMet.tanOf (hu.1 y.1 y.2).1
  let e := Equiv.ofBijective _ (get_bijective Dw)
  have hc : ∀ cf w, IsCombAtG t x (fun i : Fin (letters Dw).length => u ((letters Dw).get i).1 ((letters Dw).get i).2)
      cf w ↔ w = (tv (∑ y, cf (e.symm y) • U y)).left := fun cf w => by
    rw [← Equiv.sum_comp e]
    simp only [Equiv.symm_apply_apply]
    exact comb_iff (fun i => U (e i)) cf w
  have hτ : ∀ τ cf w, IsCombAtG t x (u τ) cf w ↔ w = (tv (∑ i, cf i • U ⟨τ, i⟩)).left := fun τ cf w =>
    comb_iff (fun i => U ⟨τ, i⟩) cf w
  refine ⟨fun cf cf' w h h' => ?_, fun j cf w h0 h => ?_⟩
  · have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
    obtain ⟨α, hinj, -, -⟩ :=
      exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
    let ρ := actR (x0 := x) (S := k) t.act
    have hE : ∀ τ (v : TanM x t.G), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV ρ (embK c τ) v ↔ ∀ a : 𝓞 E,
        (tv v).left ≫ (t.act.act a).left = spMap (epsMul (f (embK c τ a))) ≫ (tv v).left := fun τ v =>
      forall_congr' fun a => ⟨fun h => congrArg (fun z => (tv z).left) h, fun h => GlobalTheory.LieMet.tan_ext h⟩
    have hS : ∀ τ (a : Fin (Dw.mult τ) → k), ReciprocityTheory.ChartRestriction.G.PullbackSections.IsEigV ρ (embK c τ) (∑ i, a i • U ⟨τ, i⟩) := fun τ a s => by
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, (hE τ (U ⟨τ, i⟩)).2 (hu.1 τ i).2 s, smul_comm]
    have h1 := GlobalTheory.LieMet.tan_ext (((hc cf w).1 h).symm.trans ((hc cf' w).1 h'))
    rw [Fintype.sum_sigma, Fintype.sum_sigma] at h1
    funext i
    obtain ⟨⟨τ, i⟩, rfl⟩ := e.symm.surjective i
    have h2 := congrArg (proj ρ (embK c) α τ) h1
    rw [proj_sum_eig ρ (embK c) α hinj _ (fun τ' => hS τ' _), proj_sum_eig ρ (embK c) α hinj _ (fun τ' => hS τ' _)] at h2
    have h3 := hu.2 τ _ (GlobalTheory.LieMet.isTan_tv _) ((hE τ _).1 (hS τ fun i => cf (e.symm ⟨τ, i⟩)))
    exact congrFun (h3.unique ((hτ τ _ _).2 rfl) ((hτ τ _ _).2 (congrArg (fun z => (tv z).left) h2))) i
  · let B : GlobalTheory.ShFam.Pad.Letter Dw → k := fun y => if h : y.1 = ((letters Dw).get j).1 then cf (h ▸ y.2) else 0
    refine ⟨fun m => B ((letters Dw).get m), fun m hm => ?_, by simp [B], ?_⟩
    · have hp := List.pairwise_iff_get.1 (pairwise_letters Dw) j m hm
      show B ((letters Dw).get m) = 0
      revert hp
      generalize (letters Dw).get m = y
      obtain ⟨τ, i⟩ := y
      intro hp
      by_cases hy : τ = ((letters Dw).get j).1
      · subst hy
        exact (dif_pos rfl).trans (h0 _ (hp rfl))
      · exact dif_neg hy
    · rw [hc, (hτ _ _ _).1 h]
      congr 2
      have : ∀ y, (letters Dw).get (e.symm y) = y := e.apply_symm_apply
      simp only [this]
      rw [Fintype.sum_sigma, Finset.sum_eq_single ((letters Dw).get j).1]
      · exact Finset.sum_congr rfl fun i _ => by simp [B]
      · intro σ _ hσ
        exact Finset.sum_eq_zero fun i _ => by rw [show B ⟨σ, i⟩ = 0 from dif_neg hσ, zero_smul]
      · intro h; exact absurd (Finset.mem_univ _) h

end GlobalTheory.Proof.frame_combination_coeff_unique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameDomainCoordinatesHolomorphic
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.SecFrame

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FlagFibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ} (hj : j ≤ r)
  {Tau : Type} (κ : Tau ≃ X.Ψ)

def frameAt (z : Pt Tau j (r - j)) : Frame X.Ψ r := fun τ =>
  (mat (x0F X) τ * (reindex (idx hj) (idx hj)).symm (fromBlocks 1 (z (κ.symm τ)) 0 1) : Matrix (Fin r) (Fin r) ℂ)

theorem mat_frameAt (z : Pt Tau j (r - j)) (τ : X.Ψ) : mat (frameAt X hj κ z) τ =
    mat (x0F X) τ * (reindex (idx hj) (idx hj)).symm (fromBlocks 1 (z (κ.symm τ)) 0 1) := rfl

theorem frameCo_frameAt (z : Pt Tau j (r - j)) (τ : X.Ψ) :
    frameCo X hj (frameAt X hj κ z) τ = fromBlocks 1 (z (κ.symm τ)) 0 1 := by
  rw [frameCo, mat_frameAt, nonsing_inv_mul_cancel_left _ _ (det_x0F X _).isUnit, Equiv.apply_symm_apply]

theorem lminor_transpose {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i : Fin (m + 1)) : lminor Mᵀ i = lminor M i := by
  unfold lminor
  rw [← transpose_submatrix, det_transpose]

theorem frameAt_mem (hp : X.p0 = r - j) {z : Pt Tau j (r - j)} (hz : z ∈ DomI Tau j (r - j)) :
    frameAt X hj κ z ∈ X.dom := by
  intro τ
  set Z := z (κ.symm τ) with hZ
  set B : Matrix (Fin j ⊕ Fin (r - j)) (Fin j ⊕ Fin (r - j)) ℂ := fromBlocks 1 Z 0 1 with hB
  set M := (reindex (idx hj) (idx hj)).symm B with hM
  have hRM : reindex (idx hj) (idx hj) M = B := Equiv.apply_symm_apply _ _
  have hdM : M.det = 1 := by
    rw [hM, reindex_symm, det_reindex_self, hB, det_fromBlocks_zero₂₁]; simp
  refine ⟨?_, fun i => ?_⟩
  · rw [mat_frameAt, det_mul, ← hM, hdM, mul_one]; exact det_x0F X τ
  · set Dg : Matrix (Fin r) (Fin r) ℂ := diagonal fun a : Fin r => ((sgn (r - j) (a : ℕ) : ℝ) : ℂ) with hDg
    have h0 := congrArg transpose (isOrth_x0F X τ)
    rw [gram_eq_mul, diagonal_transpose, hp] at h0
    have hT : (gram τ.1 X.Gm (mat (frameAt X hj κ z) τ))ᵀ = Mᴴ * Dg * M := by
      rw [gram_eq_mul, mat_frameAt, ← hM, hDg, ← h0]
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    have hR : reindex (idx hj) (idx hj) (Mᴴ * Dg * M) = fromBlocks (-1) (-Z) (-Zᴴ) (hQ Z) := by
      have : reindex (idx hj) (idx hj) (Mᴴ * Dg * M) =
          (reindex (idx hj) (idx hj) M)ᴴ * reindex (idx hj) (idx hj) Dg * reindex (idx hj) (idx hj) M := by
        simp only [reindex_apply, conjTranspose_submatrix, submatrix_mul_equiv]
      rw [this, hRM, hDg, reindex_sgn hj, Formalism.UG.Jpq, hB, fromBlocks_neg, fromBlocks_conjTranspose, fromBlocks_multiply,
        fromBlocks_multiply]
      simp [hQ, sub_eq_neg_add]
    have hZd : (hQ Z).PosDef := hz (κ.symm τ)
    have h2 : (reindex (idx hj) (idx hj) (Mᴴ * Dg * M)).toBlocks₂₂.PosDef := by
      rw [hR, toBlocks_fromBlocks₂₂]; exact hZd
    have hs : (-schur (reindex (idx hj) (idx hj) (Mᴴ * Dg * M))).PosDef := by
      rw [hR, schur, toBlocks_fromBlocks₂₂, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁]
      have e : -(-1 - -Z * (hQ Z)⁻¹ * -Zᴴ) = (1 : Matrix (Fin j) (Fin j) ℂ) + Z * (hQ Z)⁻¹ * Zᴴ := by
        simp [Matrix.neg_mul, Matrix.mul_neg]; exact add_comm _ _
      rw [e]
      exact PosDef.add_posSemidef PosDef.one (hZd.inv.posSemidef.mul_mul_conjTranspose_same Z)
    have key := signs_of_blocks (isBlockOrderedSumEquiv_trueIndex hj) (Mᴴ * Dg * M) h2 hs i
    rw [dmin, hp, ← lminor_transpose, hT]
    exact key

theorem domPt_frameAt (z : Pt Tau j (r - j)) : domPt X hj κ (frameAt X hj κ z) = z := by
  funext t
  simp only [domPt, frameCo_frameAt, Equiv.symm_apply_apply, moeb_zero, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂,
    inv_one, Matrix.mul_one]

theorem co_frameAt (z : Pt Tau j (r - j)) (τ : X.Ψ) :
    coW X hj (frameAt X hj κ z) τ = 1 ∧ coOm X hj (frameAt X hj κ z) τ = 1 := by
  simp [coW, coOm, frameCo_frameAt, toBlocks_fromBlocks₂₁]

theorem differentiable_frameAt [Fintype Tau] (τ : X.Ψ) (a b : Fin r) :
    Differentiable ℂ (fun v : Tau × Fin j × Fin (r - j) → ℂ => mat (frameAt X hj κ (unflat v)) τ a b) := by
  have hM : ∀ c, Differentiable ℂ (fun v : Tau × Fin j × Fin (r - j) → ℂ =>
      ((reindex (idx hj) (idx hj)).symm (fromBlocks 1 (unflat v (κ.symm τ)) 0 1)) c b) := by
    intro c
    simp only [reindex_symm, reindex_apply, Equiv.symm_symm, submatrix_apply]
    rcases (idx hj) c with c' | c' <;> rcases (idx hj) b with b' | b' <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, unflat, of_apply] <;>
      first | exact differentiable_const _ | exact differentiable_apply _
  simp only [mat_frameAt, mul_apply]
  exact Differentiable.fun_sum (u := Finset.univ) (A := fun c (v : Tau × Fin j × Fin (r - j) → ℂ) =>
    mat (x0F X) τ a c * ((reindex (idx hj) (idx hj)).symm (fromBlocks 1 (unflat v (κ.symm τ)) 0 1)) c b)
    fun c _ => (hM c).const_mul _

end GlobalTheory.ShFam.SecFrame

namespace GlobalTheory.ShFam

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

theorem exists_holo_frame : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp), ∃ f : Pt D.what₂.Tau j (N - j) → (s.fd k).dom, (∀ z ∈ DomI D.what₂.Tau j (N - j), s.zOf L k (f z) = z ∧ ∀ τ, coW (s.fd k) s.j_le (f z).1 τ = 1 ∧ coOm (s.fd k) s.j_le (f z).1 τ = 1) ∧ ∀ τ a b, DifferentiableOn ℂ (fun v => ReciprocityTheory.ChartRestriction.G.FD.mat (f (unflat v)).1 τ a b) (DomFlat D.what₂.Tau j (N - j)) := by
  intro D A N j S κ s L k
  classical
  let F : Pt D.what₂.Tau j (N - j) → (s.fd k).dom := fun z =>
    if hz : z ∈ DomI D.what₂.Tau j (N - j) then
      ⟨SecFrame.frameAt (s.fd k) s.j_le (s.lab L k) z, SecFrame.frameAt_mem _ _ _ (s.p0_eq k) hz⟩
    else ⟨x0F _, IW.orth_mem_dom _ _ (isOrth_x0F _)⟩
  have hF : ∀ z ∈ DomI D.what₂.Tau j (N - j), (F z).1 = SecFrame.frameAt (s.fd k) s.j_le (s.lab L k) z :=
    fun z hz => by simp only [F, dif_pos hz]
  refine ⟨F, fun z hz => ⟨?_, fun τ => ?_⟩, fun τ a b => ?_⟩
  · show domPt (s.fd k) s.j_le (s.lab L k) (F z).1 = z
    rw [hF z hz]; exact SecFrame.domPt_frameAt _ _ _ z
  · rw [hF z hz]; exact SecFrame.co_frameAt _ _ _ z τ
  · refine (SecFrame.differentiable_frameAt (s.fd k) s.j_le (s.lab L k) τ a b).differentiableOn.congr fun v hv => ?_
    exact congrArg (fun x => ReciprocityTheory.ChartRestriction.G.FD.mat x τ a b) (hF _ hv)

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HuaIntegralPositiveDefiniteQuadricStatement
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hua_integral_positive_definite_quadric : ∀ (p q : ℕ) (A : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ), A.PosDef → ∫⁻ v : Fin p × Fin q → ℂ, ENNReal.ofReal ((shear A (toMat v)).toBlocks₂₂.det.re ^ (-((p + q : ℕ) : ℤ))) = ENNReal.ofReal (A.det.re ^ (-(q : ℤ)) / grassConst p q) := by
  first | exact @GlobalTheory.HuaQuadric.quadric | exact GlobalTheory.HuaQuadric.quadric | (intros; apply GlobalTheory.HuaQuadric.quadric <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameComposeRingHomBaseChange
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

theorem GlobalTheory.ShFam.Pad.isFrame_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (f : c.F →+* R) (φ : R →+* S) (x : Sp R ⟶ X) (u : Vecs Dw t R), GlobalTheory.LocM.IsFrame t f x u → GlobalTheory.LocM.IsFrame t (φ.comp f) (spMap φ ≫ x) (u.bc φ) :=
  GlobalTheory.LocM.isFrame_bc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPullbackOfNormalFlatProjStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_of_normal_flat_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Mdl Y i₀) (X' : Scheme.{0}) (f : X' ⟶ Z.X) (U : Z.X.Opens) (j : U.toScheme ⟶ X'), (U : Set Z.X) = Z.opn → IsProjOver (f ≫ Z.s) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' → Flat (f ≫ Z.s) → IsPullback j (𝟙 U.toScheme) f U.ι → Dense (Set.range j) → ∃ (Z' : Mdl Y i₀) (e : Z'.X ≅ X'), Z'.i = Z.i ∧ Z'.ty = Z.ty ∧ ∀ (Z₂ : Mdl Y i₀) (f₂ : X' ⟶ Z₂.X), GlobalTheory.LocM.Corr Z Z₂ → (∀ (k : Type) [Field k] (w : Sp k ⟶ U.toScheme), NatImg Z Z₂ (w ≫ U.ι) (w ≫ j ≫ f₂)) → IsMap Z' Z₂ (e.hom ≫ f₂) := by
  first | exact @GlobalTheory.LocM.Recode.exists_model_of_modification | exact GlobalTheory.LocM.Recode.exists_model_of_modification | (intros; apply GlobalTheory.LocM.Recode.exists_model_of_modification <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicFlowMajorantCauchySchwarzStatement
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlow_majorant_cauchySchwarz : FlowMajSt := by
  first | exact @GlobalTheory.CuspFrom.flowMajSt_holds | exact GlobalTheory.CuspFrom.flowMajSt_holds | (intros; apply GlobalTheory.CuspFrom.flowMajSt_holds <;> assumption)
end

