import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsVarietyFlagRefinementBundleOfGoodModel
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

variable {F : Type} [Field F] {Ω Ω' : Type} [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']

private theorem eq_spMap_of_specializes {X : Scheme.{0}} {K : Type} [Field K] (g : Sp K ⟶ X) {z : X}
    (h : g (IsLocalRing.closedPoint K) ⤳ z) :
    g = spMap (X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of K) g).hom ≫
      X.fromSpecStalk z := by
  conv_lhs => rw [← spMap_stalkClosedPointTo g]
  rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
  show Spec.map _ ≫ _ = Spec.map _ ≫ _
  simp only [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc]

private theorem spMap_comp_spMap_divisor {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem exists_isHom_of_generic (M : RatModel F Ω) (M' : RatModel F Ω') (f : M'.Z ⟶ M.Z) (hs : f ≫ M.s = M'.s)
    (hg : f (genericPoint M'.Z) = genericPoint M.Z) : ∃ φ : Ω →ₐ[F] Ω', M.IsHom M' φ f := by
  classical
  have hp0 : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') = genericPoint M.Z := by
    have h1 : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') = f (M'.pt (IsLocalRing.closedPoint Ω')) := rfl
    rw [h1]
    exact (congrArg f (M'.pt_apply (IsLocalRing.closedPoint Ω'))).trans hg
  have hp : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') ⤳ genericPoint M.Z := by rw [hp0]
  have hq : M.pt = spMap (M.stalkHom (genericPoint M.Z)) ≫ M.Z.fromSpecStalk (genericPoint M.Z) :=
    eq_spMap_of_specializes M.pt (M.pt_specializes (IsLocalRing.closedPoint Ω) (genericPoint M.Z))
  have hsurj : Function.Surjective (M.stalkHom (genericPoint M.Z)) := by
    intro x
    have hx : x ∈ M.O (genericPoint M.Z) := by rw [M.O_genericPoint]; exact Algebra.mem_top
    obtain ⟨a, ha⟩ := (M.stalkEquiv (genericPoint M.Z)).surjective ⟨x, hx⟩
    refine ⟨a, ?_⟩
    rw [← RatModel.coe_stalkEquiv, ha]
  let E := RingEquiv.ofBijective (M.stalkHom (genericPoint M.Z)) ⟨M.stalkHom_injective _, hsurj⟩
  let α := (M.Z.presheaf.stalkSpecializes hp ≫
    Scheme.stalkClosedPointTo (R := CommRingCat.of Ω') (M'.pt ≫ f)).hom
  let φ₀ : Ω →+* Ω' := α.comp E.symm.toRingHom
  have key : φ₀.comp (M.stalkHom (genericPoint M.Z)) = α := by
    ext a
    show α (E.symm (E a)) = α a
    rw [E.symm_apply_apply]
  have hpt : M'.pt ≫ f = spMap φ₀ ≫ M.pt := by
    rw [eq_spMap_of_specializes (M'.pt ≫ f) hp, hq, ← Category.assoc, ← spMap_comp_spMap_divisor, key]
  have hc : spMap (φ₀.comp (algebraMap F Ω)) = spMap (algebraMap F Ω') := by
    rw [spMap_comp_spMap_divisor, ← M.pt_s, ← Category.assoc, ← hpt, Category.assoc, hs, M'.pt_s]
  have hinj : φ₀.comp (algebraMap F Ω) = algebraMap F Ω' := by
    have h2 : CommRingCat.ofHom (φ₀.comp (algebraMap F Ω)) = CommRingCat.ofHom (algebraMap F Ω') :=
      Spec.map_injective hc
    ext a
    exact congrArg (fun g => g.hom a) h2
  exact ⟨⟨φ₀, fun a => RingHom.congr_fun hinj a⟩, hpt⟩

theorem apply_eq_of_isHom_id {M : RatModel F Ω} {χ : Ω →ₐ[F] Ω} (h : M.IsHom M χ (𝟙 M.Z)) (x : Ω) : χ x = x := by
  have hpt : (𝟙 M.Z : M.Z ⟶ M.Z) (M.pt (IsLocalRing.closedPoint Ω)) = genericPoint M.Z := by
    exact M.pt_apply _
  have hx : x ∈ M.O ((𝟙 M.Z : M.Z ⟶ M.Z) (M.pt (IsLocalRing.closedPoint Ω))) := by
    rw [hpt, M.O_genericPoint]; exact Algebra.mem_top
  have h2 := h.val_comp M.pt (IsLocalRing.closedPoint Ω) hx
  rw [Category.comp_id, RatModel.val_pt, RatModel.val_pt] at h2
  exact h2.symm

theorem iso_genericPoint {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (e : X ≅ Y) :
    e.hom (genericPoint X) = genericPoint Y := by
  exact genericPoint_eq_of_isOpenImmersion e.hom

private theorem mat_map_mul_inv {ι : Type} {m : ι → ℕ} {K K' : Type} [Field K] [Field K'] (σ : K →+* K')
    (X Y : Mat m K) : (X * Y⁻¹).map σ = X.map σ * (Y.map σ)⁻¹ := by
  rw [Mat.map_mul, Mat.map_inv]

theorem exists_refines_of_iso {ι : Type} {m k : ι → ℕ} (M : RatModel F Ω) (M' : RatModel F Ω') (e : M'.Z ≅ M.Z)
    (hs : e.hom ≫ M.s = M'.s) (S : Fr M m k) :
    ∃ (φ : Ω →ₐ[F] Ω') (S' : Fr M' m k), Refines S S' φ e.hom := by
  classical
  obtain ⟨φ, hφ⟩ := exists_isHom_of_generic M M' e.hom hs (iso_genericPoint e)
  have hs' : e.inv ≫ M'.s = M.s := by rw [← hs, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  obtain ⟨ψ, hψ⟩ := exists_isHom_of_generic M' M e.inv hs' (iso_genericPoint e.symm)
  have hid : M.IsHom M (ψ.comp φ) (𝟙 M.Z) := by
    have h1 := hφ.comp hψ
    rwa [e.inv_hom_id] at h1
  have hid' : M'.IsHom M' (φ.comp ψ) (𝟙 M'.Z) := by
    have h1 := hψ.comp hφ
    rwa [e.hom_inv_id] at h1
  have hψφ : ∀ x, ψ (φ x) = x := fun x => apply_eq_of_isHom_id hid x
  have hφψ : ∀ x, φ (ψ x) = x := fun x => apply_eq_of_isHom_id hid' x
  have pt2 : ∀ z' : M'.Z, e.inv (e.hom z') = z' := fun z' => by simp
  have memφ : ∀ {z' : M'.Z} {x : Ω}, x ∈ M.O (e.hom z') → φ x ∈ M'.O z' := fun hx => hφ.map_mem_O hx
  have memψ : ∀ {z' : M'.Z} {x : Ω'}, x ∈ M'.O z' → ψ x ∈ M.O (e.hom z') := by
    intro z' x hx
    apply hψ.map_mem_O
    rwa [pt2]
  have mm1 : ∀ g : Mat m Ω, (g.map φ).map ψ = g := by
    intro g; funext τ; ext i j; simp [Mat.map, hψφ]
  have mm2 : ∀ g : Mat m Ω', (g.map ψ).map φ = g := by
    intro g; funext τ; ext i j; simp [Mat.map, hφψ]
  have I1 : ∀ (B : Mat m Ω') (A : Mat m Ω), B.map ψ * A⁻¹ = (B * (A.map φ)⁻¹).map ψ := by
    intro B A
    have h1 := mat_map_mul_inv ψ.toRingHom B (A.map φ)
    have h2 : (B * (A.map φ)⁻¹).map ψ = B.map ψ * ((A.map φ).map ψ)⁻¹ := h1
    rw [h2, mm1]
  have I2 : ∀ (B : Mat m Ω') (A : Mat m Ω), (B.map ψ * A⁻¹).map φ = B * (A.map φ)⁻¹ := by
    intro B A
    have h1 := mat_map_mul_inv φ.toRingHom (B.map ψ) A
    have h2 : (B.map ψ * A⁻¹).map φ = (B.map ψ).map φ * (A.map φ)⁻¹ := h1
    rw [h2, mm2]
  have hdet : ∀ {A : Mat m Ω}, (∀ τ, (A τ).det ≠ 0) → ∀ τ, ((A.map φ) τ).det ≠ 0 := by
    intro A hA τ
    have h1 : ((A.map φ) τ).det = φ (A τ).det := Mat.det_map A φ.toRingHom τ
    rw [h1]
    exact (map_ne_zero φ).2 (hA τ)
  let S' : Fr M' m k :=
    { S := fun z' => {A' | A'.map ψ ∈ S.S (e.hom z')}
      loc := by
        intro z'
        obtain ⟨U, A, hzU, hA, hU⟩ := S.loc (e.hom z')
        refine ⟨e.hom ⁻¹ᵁ U, A.map φ, hzU, hdet hA, fun z'' hz'' A'' => ?_⟩
        show A''.map ψ ∈ S.S (e.hom z'') ↔ _
        rw [hU (e.hom z'') hz'' (A''.map ψ), I1]
        constructor
        · intro h
          have h1 : Par k (M'.O z'').toSubring (((A'' * (A.map φ)⁻¹).map ψ).map φ) :=
            h.map φ.toRingHom (fun x hx => memφ hx)
          rwa [mm2] at h1
        · intro h
          exact h.map ψ.toRingHom (fun x hx => memψ hx) }
  refine ⟨φ, S', ⟨le_rfl, hφ, ?_, ?_, ?_⟩⟩
  · intro z' A' hA' A hA
    have h1 : Par k (M.O (e.hom z')).toSubring (A'.map ψ * A⁻¹) :=
      (Fr.mem_iff hA).1 (show A'.map ψ ∈ S.S (e.hom z') from hA')
    have h2 : Par k (M'.O z').toSubring ((A'.map ψ * A⁻¹).map φ) :=
      h1.map φ.toRingHom (fun x hx => memφ hx)
    rwa [I2] at h2
  · unfold KeepsRad Rad
    intro z' g hg
    obtain ⟨hg0, hgO, hgr⟩ := hg
    refine ⟨(map_ne_zero φ).2 hg0, memφ hgO, fun x n hx hxn => ?_⟩
    have hx' : ψ x ∈ M.O (e.hom z') := memψ hx
    have hxn' : ψ x ^ n / g ∈ M.O (e.hom z') := by
      have h1 := memψ hxn
      rw [map_div₀, map_pow, hψφ] at h1
      exact h1
    have h2 := memφ (hgr (ψ x) n hx' hxn')
    rw [map_div₀, hφψ] at h2
    exact h2
  · intro K _ x A hA h hh
    refine ⟨x ≫ e.inv, ⟨by simp, ?_⟩, fun p hp => ?_⟩
    · have hx1 : e.hom ((x ≫ e.inv) (IsLocalRing.closedPoint K)) = x (IsLocalRing.closedPoint K) := by
        have h1 : (x ≫ e.inv) (IsLocalRing.closedPoint K) = e.inv (x (IsLocalRing.closedPoint K)) := rfl
        rw [h1]
        simp
      have hd : ∀ τ, ((A.map φ) τ).det ≠ 0 := hdet (Fr.det_ne hA)
      have hone : (1 : Mat m Ω').map (M'.val (x ≫ e.inv)) = 1 := by
        funext τ; ext i j
        simp only [Mat.map, Matrix.map_apply, Pi.one_apply, Matrix.one_apply]
        split_ifs
        · exact RatModel.val_one _
        · exact RatModel.val_zero _
      have hinv : (1 : Mat m K)⁻¹ = 1 := by
        have h1 := Mat.mul_inv (g := (1 : Mat m K)) (fun τ => by simp)
        rwa [one_mul] at h1
      unfold Bears
      refine ⟨A.map φ, ?_, ?_⟩
      · show (A.map φ).map ψ ∈ S.S (e.hom ((x ≫ e.inv) (IsLocalRing.closedPoint K)))
        rw [mm1, hx1]
        exact hA
      · rw [Mat.mul_inv hd, hone, hinv, mul_one]
        exact hh
    · rw [← hp.1, Category.assoc, e.hom_inv_id, Category.comp_id]

theorem exists_var_refines (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) (ι : Type)
    (m k : ι → ℕ) (S : Fr M m k) (h : Good M d) :
    ∃ (Y : GlobalTheory.ProjVar.Var F) (φ : Ω →ₐ[F] Y.Fn) (f : Y.X ⟶ M.Z) (S' : Fr (ratOf Y) m k),
      Y.dim = d ∧ Refines S S' φ f := by
  obtain ⟨hP, hSm, hGI⟩ := h
  haveI : SmoothOfRelativeDimension d M.s := hSm
  haveI : GeometricallyIntegral M.s := hGI
  haveI : GeometricallyConnected M.s := by
    constructor
    intro a b y c fst snd hpb
    have := GeometricallyIntegral.geometrically_isIntegral (f := M.s) y fst snd hpb
    infer_instance
  obtain ⟨Y, e, hd, he⟩ := GlobalTheory.ProjVar.Var.exists_iso M.s d hP
  have hs : e.inv ≫ M.s = (ratOf Y).s := by
    show e.inv ≫ M.s = Y.str
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  obtain ⟨φ, S', hS'⟩ := exists_refines_of_iso M (ratOf Y) e.symm hs S
  exact ⟨Y, φ, e.inv, S', hd, hS'⟩

end GlobalTheory.FlagBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedPlaceUnitaryLocalPointsEquivLocalUnitaryGro
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.Mem.Chr

namespace GlobalTheory.DefU.Inert

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conjPl_self (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) : ConjPl (IsCMField.complexConj E).toRingEquiv w w := fun k => by
  have h1 : Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
    w.valuedAdicCompletion_eq_valuation' k
  have h2 : Valued.v (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E k)) =
      w.valuation E (IsCMField.complexConj E k) := w.valuedAdicCompletion_eq_valuation' _
  have h3 := hv (algebraMap E (w.adicCompletion E) k)
  rw [hs, h1, h2] at h3
  exact h3

theorem eq_of_under_eq {w u : HeightOneSpectrum (𝓞 E)} (hw : ConjPl (IsCMField.complexConj E).toRingEquiv w w)
    (hu : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) : u = w := by
  rcases (under_eq_iff_conjPl (IsCMField.complexConj E) (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
    (IsCMField.complexConj_ne_one E) w u).1 hu with h | h
  · exact h
  · exact (existsUnique_conjPl _ w).unique h hw

theorem continuous_finGL : Continuous (finGL E n) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))

theorem continuous_cLoc (w : HeightOneSpectrum (𝓞 E)) : Continuous (cLoc (n := n) w) :=
  (Continuous.units_map _ (continuous_id.matrix_map
    ((RestrictedProduct.continuous_eval w).comp continuous_snd))).comp continuous_subtype_val

theorem mat_ext {A B : Matrix (Fin n) (Fin n) (Ad E)} (h1 : A.map (pInf E) = B.map (pInf E))
    (h2 : ∀ v, A.map ((pLoc E v).comp (pFin E)) = B.map ((pLoc E v).comp (pFin E))) : A = B := by
  ext i j
  refine ad_ext (congrFun (congrFun h1 i) j) (FiniteAdeleRing.ext _ fun v => ?_)
  exact congrFun (congrFun (h2 v) i) j

theorem map_finGL (v : HeightOneSpectrum (𝓞 E)) (k : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E n k) = GeneralLinearGroup.map (pLoc E v) k :=
  Units.ext (congrArg (fun g : GL (Fin n) (v.adicCompletion E) => (g : Matrix (Fin n) (Fin n) (v.adicCompletion E)))
    (congrArg (GeneralLinearGroup.map (pLoc E v)) (pFin_finGL k)))

theorem pInf_conjAd (x : Ad E) : pInf E (conjAd E x) = star (pInf E x) :=
  (infEq E).symm_apply_apply _

theorem finGL_mem (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) (g : GL (Fin n) (w.adicCompletion E))
    (hg : g ∈ UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) :
    finGL E n (locGL E n w g) ∈ UA E n := by
  have hg' : cT s g.val * g.val = 1 := by
    have h : cT s g.val * 1 * g.val = 1 := hg
    rwa [Matrix.mul_one] at h
  have hw := conjPl_self w s hs hv
  change cT (conjAd E) (finGL E n (locGL E n w g)).val * 1 * (finGL E n (locGL E n w g)).val = 1
  rw [Matrix.mul_one]
  generalize hh : finGL E n (locGL E n w g) = h
  have hI : h.val.map (pInf E) = 1 := by
    rw [← hh]
    exact congrArg Units.val (pInf_finGL (locGL E n w g))
  have hL : ∀ v, h.val.map ((pLoc E v).comp (pFin E)) =
      (GeneralLinearGroup.map (pLoc E v) (locGL E n w g)).val := fun v => by
    rw [← hh]
    exact congrArg Units.val (map_finGL v (locGL E n w g))
  refine mat_ext ?_ fun v => ?_
  · have hc : (cT (conjAd E) h.val).map (pInf E) = 1 := by
      refine Matrix.ext fun i j => ?_
      have h1 : pInf E (h.val j i) = (1 : Matrix (Fin n) (Fin n) (Cinf E)) j i := congrFun (congrFun hI j) i
      change pInf E (conjAd E (h.val j i)) = _
      rw [pInf_conjAd, h1]
      by_cases e : i = j
      · subst e; simp
      · simp [Matrix.one_apply, e, Ne.symm e]
    rw [Matrix.map_mul, hc, hI, Matrix.mul_one, Matrix.map_one _ (map_zero _) (map_one _)]
  · rcases eq_or_ne v w with rfl | hvw
    · have h0 := hL v
      rw [pLoc_locGL] at h0
      have hc : (cT (conjAd E) h.val).map ((pLoc E v).comp (pFin E)) = cT s g.val := by
        refine Matrix.ext fun i j => ?_
        have h1 : pLoc E v (pFin E (h.val j i)) = g.val j i := congrFun (congrFun h0 j) i
        change pLoc E v (conjFin (IsCMField.complexConj E).toRingEquiv (pFin E (h.val j i))) = s (g.val j i)
        rw [pLoc_conjFin_eq _ v s hs hv, h1]
      rw [Matrix.map_mul, hc, h0, hg', Matrix.map_one _ (map_zero _) (map_one _)]
    · have h0 := hL v
      rw [pLoc_locGL_of_ne hvw] at h0
      have hne : conjSrc (IsCMField.complexConj E).toRingEquiv v ≠ w := fun e =>
        hvw ((existsUnique_conjPl _ w).unique (e ▸ conjPl_conjSrc _ v) hw)
      have h2 := hL (conjSrc (IsCMField.complexConj E).toRingEquiv v)
      rw [pLoc_locGL_of_ne hne] at h2
      have hc : (cT (conjAd E) h.val).map ((pLoc E v).comp (pFin E)) = 1 := by
        refine Matrix.ext fun i j => ?_
        have h1 : pLoc E (conjSrc (IsCMField.complexConj E).toRingEquiv v) (pFin E (h.val j i)) =
            (1 : Matrix (Fin n) (Fin n) _) j i := congrFun (congrFun h2 j) i
        change pLoc E v (conjFin (IsCMField.complexConj E).toRingEquiv (pFin E (h.val j i))) = _
        rw [pLoc_conjFin, h1]
        by_cases e : i = j
        · subst e; simp
        · simp [Matrix.one_apply, e, Ne.symm e]
      have h0' : h.val.map ((pLoc E v).comp (pFin E)) = 1 := h0
      rw [Matrix.map_mul, hc, h0', Matrix.mul_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem finGL_mem_locU {w : HeightOneSpectrum (𝓞 E)} (hw : ConjPl (IsCMField.complexConj E).toRingEquiv w w)
    (g : GL (Fin n) (w.adicCompletion E)) (hU : finGL E n (locGL E n w g) ∈ UA E n) :
    (⟨_, hU⟩ : UA E n) ∈ locU n w := by
  refine Subgroup.mem_inf.2 ⟨pInf_finGL _, ?_⟩
  simp only [Subgroup.mem_iInf]
  intro u hu
  have hne : u ≠ w := fun e => hu (by rw [e])
  exact (map_finGL u _).trans (pLoc_locGL_of_ne hne g)

theorem finGL_cLoc {w : HeightOneSpectrum (𝓞 E)} (hw : ConjPl (IsCMField.complexConj E).toRingEquiv w w)
    (x : locU n w) : finGL E n (locGL E n w (cLoc w (x : UA E n))) = (x : UA E n).1 := by
  have hx := Subgroup.mem_inf.1 x.2
  have hx2 := hx.2
  simp only [Subgroup.mem_iInf] at hx2
  refine Units.ext (mat_ext ?_ fun v => ?_)
  · have h1 : GeneralLinearGroup.map (pInf E) (x : UA E n).1 = 1 := hx.1
    have h2 := pInf_finGL (locGL E n w (cLoc w (x : UA E n)))
    exact congrArg Units.val (h2.trans h1.symm)
  · have h1 : GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E n (locGL E n w (cLoc w (x : UA E n)))) =
        GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (x : UA E n).1 := by
      refine (map_finGL v _).trans ?_
      rcases eq_or_ne v w with rfl | hvw
      · exact pLoc_locGL v _
      · rw [pLoc_locGL_of_ne hvw]
        have := hx2 v fun e => hvw (eq_of_under_eq hw e)
        exact (MonoidHom.mem_ker.1 this).symm
    exact congrArg Units.val h1

theorem locU_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (s : w.adicCompletion E →+* w.adicCompletion E),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) →
    (∀ x, Valued.v (s x) = Valued.v x) →
    ∃ e : locU n w ≃ₜ* UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)),
      ∀ x : locU n w, (e x : GL (Fin n) (w.adicCompletion E)) = cLoc w (x : UA E n) := by
  intro E _ _ _ n w s hs hv
  have hw := conjPl_self w s hs hv
  have hf : ∀ x : locU n w, cLoc w (x : UA E n) ∈ UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := fun x => by
    change cT s _ * 1 * _ = 1
    rw [Matrix.mul_one]
    exact cT_cLoc w s hs hv _
  refine ⟨{ toFun := fun x => ⟨cLoc w (x : UA E n), hf x⟩
            invFun := fun g => ⟨⟨finGL E n (locGL E n w g.1), finGL_mem w s hs hv g.1 g.2⟩,
              finGL_mem_locU hw g.1 _⟩
            left_inv := fun x => Subtype.ext (Subtype.ext (finGL_cLoc hw x))
            right_inv := fun g => Subtype.ext ?_
            map_mul' := fun x y => Subtype.ext (map_mul (cLoc w) (x : UA E n) y)
            continuous_toFun := Continuous.subtype_mk ((continuous_cLoc w).comp continuous_subtype_val) _
            continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk
              (continuous_finGL.comp ((CuspSub.continuous_locGL w).comp continuous_subtype_val)) _) _ }, fun _ => rfl⟩
  exact (map_finGL w _).trans (pLoc_locGL w _)

end GlobalTheory.DefU.Inert

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricallyIntegral
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier
open scoped TensorProduct

variable {F Ω Ω' : Type} [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']

theorem exists_openImmersion_ringOn (M : RatModel F Ω) {U : M.Z.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set M.Z).Nonempty) : ∃ ι : Sp (M.ringOn U) ⟶ M.Z, IsOpenImmersion ι ∧ Set.range ι = U ∧
      ι ≫ M.s = spMap (algebraMap F (M.ringOn U)) := by
  let e : Γ(M.Z, U) ≅ CommRingCat.of (M.ringOn U) := (M.sectionsEquiv U hne).toCommRingCatIso
  have hx := GlobalTheory.Points.le_preimage_specMap_fromSpec hU e.hom
  have hv : ∀ f, valR (Spec.map e.hom ≫ hU.fromSpec) U f = M.sectionsEquiv U hne f := fun f => by
    rw [GlobalTheory.Points.valR_eq _ U hx, GlobalTheory.Points.valMap_specMap_fromSpec]
    rfl
  refine ⟨Spec.map e.hom ≫ hU.fromSpec, inferInstance, ?_, ?_⟩
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, (Spec.map e.hom).surjective.range_eq,
      Set.image_univ, hU.range_fromSpec]
  · rw [← Spec.map_preimage ((Spec.map e.hom ≫ hU.fromSpec) ≫ M.s)]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun b => ?_))
    rw [← GlobalTheory.Points.valR_constFn M.s _ U hx, hv]
    exact Subtype.ext ((RatModel.coe_sectionsEquiv U hne _).trans (M.valF_constFn hne b))

theorem exists_openImmersion_tensor (M : RatModel F Ω) {U : M.Z.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set M.Z).Nonempty) {K : Type} [Field K] [Algebra F K] {Z : Scheme.{0}} {p : Z ⟶ M.Z} {q : Z ⟶ Sp K}
    (h : IsPullback p q M.s (spMap (algebraMap F K))) :
    ∃ j : Sp (M.ringOn U ⊗[F] K) ⟶ Z, IsOpenImmersion j ∧ Set.range j = p ⁻¹' U := by
  obtain ⟨ι, hι, hr, hs⟩ := exists_openImmersion_ringOn M hU hne
  have h1 := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct F (M.ringOn U) K)
  rw [show Spec.map (CommRingCat.ofHom (algebraMap F (M.ringOn U))) = ι ≫ M.s from hs.symm] at h1
  let j := h.lift (_ ≫ ι) _ ((Category.assoc _ _ _).trans h1.w)
  have h2 : IsPullback j _ p ι :=
    (IsPullback.of_bot (h₁₁ := _) (by simpa [j] using h1) (h.lift_fst _ _ _).symm h).flip
  refine ⟨j, MorphismProperty.of_isPullback h2.flip hι, ?_⟩
  refine Eq.trans ?_ (congrArg (p ⁻¹' ·) hr)
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, by rw [← Scheme.Hom.comp_apply, ← h2.w, Scheme.Hom.comp_apply]⟩
  · rintro ⟨w, hw⟩
    obtain ⟨v, hv, -⟩ := Scheme.exists_preimage_of_isPullback h2 z w hw.symm
    exact ⟨v, hv⟩

theorem nonempty_algEquiv_adjoin (φ : Ω →ₐ[F] Ω') (A : Subalgebra F Ω) {σ : Type} (t : σ → Ω')
    (ht : ∀ P : MvPolynomial σ Ω, MvPolynomial.eval₂ (φ : Ω →+* Ω') t P = 0 → P = 0) :
    Nonempty (MvPolynomial σ A ≃ₐ[F] Algebra.adjoin F (φ '' (A : Set Ω) ∪ Set.range t)) := by
  let ψ : MvPolynomial σ A →ₐ[F] Ω' := MvPolynomial.aevalTower (φ.comp A.val) t
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro P hP
    refine MvPolynomial.map_injective (A.val : A →+* Ω) Subtype.val_injective ?_
    rw [map_zero]
    refine ht _ ?_
    rw [MvPolynomial.eval₂_map]
    exact hP
  have hr : ψ.range = Algebra.adjoin F (φ '' (A : Set Ω) ∪ Set.range t) := by
    refine le_antisymm ?_ (Algebra.adjoin_le ?_)
    · rintro _ ⟨P, rfl⟩
      show ψ P ∈ _
      induction P using MvPolynomial.induction_on with
      | C a => exact Algebra.subset_adjoin (Or.inl ⟨a, a.2, by simp [ψ]⟩)
      | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
      | mul_X P i hP =>
        rw [map_mul]
        exact mul_mem hP (Algebra.subset_adjoin (Or.inr ⟨i, by simp [ψ]⟩))
    · rintro _ (⟨a, ha, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨MvPolynomial.C ⟨a, ha⟩, by simp [ψ]⟩
      · exact ⟨MvPolynomial.X i, by simp [ψ]⟩
  exact ⟨(AlgEquiv.ofInjective ψ hinj).trans (Subalgebra.equivOfEq _ _ hr)⟩

theorem isDomain_mvPolynomial_tensor (A K σ : Type) [CommRing A] [Algebra F A] [CommRing K] [Algebra F K]
    [IsDomain (A ⊗[F] K)] : IsDomain (MvPolynomial σ A ⊗[F] K) := by
  let e1 : MvPolynomial σ A ⊗[F] K ≃ₐ[F] (A ⊗[F] MvPolynomial σ F) ⊗[F] K :=
    Algebra.TensorProduct.congr ((MvPolynomial.algebraTensorAlgEquiv F A).symm.restrictScalars F) AlgEquiv.refl
  let e2 : (A ⊗[F] MvPolynomial σ F) ⊗[F] K ≃ₐ[F] (A ⊗[F] K) ⊗[F] MvPolynomial σ F :=
    (Algebra.TensorProduct.assoc F F F A (MvPolynomial σ F) K).trans
      ((Algebra.TensorProduct.congr AlgEquiv.refl (Algebra.TensorProduct.comm F _ _)).trans
        (Algebra.TensorProduct.assoc F F F A K (MvPolynomial σ F)).symm)
  let e3 := MvPolynomial.algebraTensorAlgEquiv (σ := σ) F (A ⊗[F] K)
  exact (((e1.trans e2).toRingEquiv).trans e3.toRingEquiv).toMulEquiv.isDomain _

theorem AffCover.geometricallyIntegral : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r : ℕ), AffCover M M' φ f r →
    GeometricallyIntegral M.s → GeometricallyIntegral M'.s := by
  intro F Ω Ω' _ _ _ _ _ M M' φ f r h hM
  refine ⟨geometrically_iff_of_commRing.2 fun K _ _ Z p q hZ => ?_⟩
  have hI : IsIntegral (pullback M.s (spMap (algebraMap F K))) :=
    pullback_of_geometrically hM.geometrically_isIntegral K _
  have key : ∀ z' : M'.Z, ∃ (U : M'.Z.Opens) (Y : Scheme.{0}) (j : Y ⟶ Z), z' ∈ U ∧ IsIntegral Y ∧
      IsOpenImmersion j ∧ Set.range j = p ⁻¹' U := by
    intro z'
    obtain ⟨U, W, t, hU, hW, hz, hUW, ht, hR⟩ := h.2 z'
    have hWne : (W : Set M.Z).Nonempty := ⟨_, hUW z' hz⟩
    obtain ⟨i, hi, -⟩ := exists_openImmersion_tensor M hW hWne (IsPullback.of_hasPullback M.s (spMap (algebraMap F K)))
    have : Nontrivial (M.ringOn W ⊗[F] K) := inferInstance
    have : IsIntegral (Sp (M.ringOn W ⊗[F] K)) := isIntegral_of_isOpenImmersion i
    have : IsDomain (M.ringOn W ⊗[F] K) := (affine_isIntegral_iff (CommRingCat.of _)).1 this
    have := isDomain_mvPolynomial_tensor (F := F) (M.ringOn W) K (Fin r)
    obtain ⟨e⟩ := nonempty_algEquiv_adjoin φ (M.ringOn W) t ht
    rw [← hR] at e
    have : IsDomain (M'.ringOn U ⊗[F] K) :=
      (Algebra.TensorProduct.congr e.symm (AlgEquiv.refl (A₁ := K) (R := F))).toMulEquiv.isDomain _
    obtain ⟨j, hj, hr⟩ := exists_openImmersion_tensor M' hU ⟨_, hz⟩ hZ
    exact ⟨U, _, j, hz, inferInstance, hj, hr⟩
  have hred : IsReduced Z := by
    have : ∀ z : Z, _root_.IsReduced (Z.presheaf.stalk z) := fun z => by
      obtain ⟨U, Y, j, hz, hY, hj, hr⟩ := key (p z)
      obtain ⟨y, rfl⟩ : z ∈ Set.range j := hr ▸ hz
      exact isReduced_of_injective (j.stalkMap y).hom (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv.injective
    exact isReduced_of_isReduced_stalk Z
  have hopen : UniversallyOpen p := MorphismProperty.of_isPullback hZ.flip inferInstance
  have hirr : IrreducibleSpace Z := by
    obtain ⟨U, Y, j, hz, hY, hj, hr⟩ := key (genericPoint M'.Z)
    have h1 : IsIrreducible (Set.range j) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ Y).image _ j.continuous.continuousOn
    have h2 : Dense (Set.range j) := by
      rw [hr]
      exact (U.isOpen.dense ⟨_, hz⟩).preimage p.isOpenMap
    have h3 := h1.closure
    rw [h2.closure_eq] at h3
    exact (irreducibleSpace_def Z).2 h3
  exact isIntegral_of_irreducibleSpace_of_isReduced Z

end GlobalTheory.FlagBundle
end
end

