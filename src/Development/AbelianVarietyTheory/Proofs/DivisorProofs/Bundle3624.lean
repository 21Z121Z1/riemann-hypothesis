import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3617
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3619
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0789
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2301
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2299
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2298
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3618
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2745
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsPerfectOfIsDual
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3620
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistAtEach
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3562

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerInteriorAffineOpen
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

namespace GlobalTheory.KSInterior

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_sab_chartPull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ (t' : SAB H S') (m : SABMap t' t f), Nonempty (ChartPull t'.PP.L t.PP.L m.φ) := by
  have h := isGrpPullback_pullback t.G f
  obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := Out.CubePf.cubePull S S' t.G _ (cubeMapOf h) t.PP t.cub
  have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
      pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj t.G) a,
      pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  refine ⟨⟨(Over.pullback f).obj t.G, IsSemiAbelian.pullback f t.G t.semi, OAct.pullback f t.G t.act,
    (cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_⟩, ⟨cubeMapOf h, h, rfl, hact, hc'⟩,
    ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.PP.L _ _ rfl⟩⟩
  · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
      (pushPt h.1.w (snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
    refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
    · fin_cases i
      · exact (pa _ a).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa _ _).trans (by simp [U])
  · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
    refine LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.PP.L _ U.left (Category.id_comp _))
      (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
    fin_cases i
    · simp [U]
    · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)

end GlobalTheory.KSInterior

namespace GlobalTheory.KSInterior

theorem exists_derivation_transport {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (D : Derivation ℤ A A) :
    ∃ D' : Derivation ℤ B B, ∀ r, D' (e r) = e (D r) := by
  let f : B →ₗ[ℤ] B :=
    { toFun := fun b => e (D (e.symm b)), map_add' := fun a b => by simp, map_smul' := fun k b => by simp }
  refine ⟨{ toLinearMap := f, map_one_eq_zero' := by simp [f], leibniz' := fun a b => ?_ }, fun r => by simp [f]⟩
  simp only [f, LinearMap.coe_mk, AddHom.coe_mk, map_mul, Derivation.leibniz, smul_eq_mul, map_add,
    RingEquiv.apply_symm_apply]

end GlobalTheory.KSInterior

namespace GlobalTheory.KSInterior

theorem isKS_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) [IsOpenImmersion j] (m : SABMap t' t j), Nonempty (ChartPull t'.PP.L t.PP.L m.φ) → ∀ (V : X.Opens) (W : X.affineOpens) (W' : X'.affineOpens) (hW' : W'.1 = j ⁻¹ᵁ W.1), Function.Bijective (j.appLE W.1 W'.1 hW'.le).hom → W.1 ≤ V → W.1 ≤ j.opensRange → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, W.1)) ⟶ t.G.left)) (v' : Fin n → (Sp (DualNumber Γ(X', W'.1)) ⟶ t'.G.left)), (∀ i, IsTanAtG t (chart W) (v i)) → (∀ i, IsTanAtG t' (chart W') (v' i)) → (∀ i, v' i ≫ m.φ = spMap (dualMap (j.appLE W.1 W'.1 hW'.le).hom) ≫ v i) → ∀ (D : Γ(X, W.1) → Γ(X, W.1)) (D' : Γ(X', W'.1) → Γ(X', W'.1)), (∀ r, D' ((j.appLE W.1 W'.1 hW'.le).hom r) = (j.appLE W.1 W'.1 hW'.le).hom (D r)) → ∀ Θ' : Matrix (Fin n) (Fin n) Γ(X', W'.1), IsKS t' ⊤ W' v' D' Θ' → ∃ Θ, IsKS t V W v D Θ := by
  intro E _ _ _ H X X' t t' j _ m hcp V W W' hW' hbij hWV hWr n v v' hv hv't hvv D D' hD Θ' hKS
  obtain ⟨cp⟩ := hcp
  obtain ⟨J, Wc, jj, d, hsup, hj, hfld, hcomp, htest⟩ := hKS
  obtain ⟨hφo, hφr⟩ := GlobalTheory.T.semiAbelianTripleMap_isOpenImmersion_opensRange E H X X' t t' j m
  set ψ := j.appLE W.1 W'.1 hW'.le with hψ
  let e := RingEquiv.ofBijective ψ.hom hbij
  have sq : m.φ ≫ t.G.hom = t'.G.hom ≫ j := m.cart.1.w
  have hx : chart W' ≫ j = spMap ψ.hom ≫ chart W :=
    (IsAffineOpen.SpecMap_appLE_fromSpec j W.2 W'.2 hW'.le).symm
  have hWc : ∀ i, Wc i ≤ t'.G.hom ⁻¹ᵁ W'.1 := fun i =>
    (le_iSup Wc i).trans (hsup.le.trans (t'.G.hom.preimage_mono inf_le_left))
  choose d₂ hd₂F hd₂ using fun i => GlobalTheory.T.exists_vectorField_image_openImmersion _ _ m.φ (Wc i) (d i) (hfld i)
  have hpi : ∀ i, m.φ ⁻¹ᵁ (m.φ ''ᵁ Wc i) = Wc i := fun i => m.φ.preimage_image_eq (Wc i)
  have cong : ∀ {A B : Scheme.{0}} {f g : A ⟶ B} (_ : f = g) (U : B.Opens) (U' : A.Opens) (p₁ : U' ≤ f ⁻¹ᵁ U)
      (p₂ : U' ≤ g ⁻¹ᵁ U), f.appLE U U' p₁ = g.appLE U U' p₂ := by
    intros; subst_vars; rfl
  have happ : ∀ (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ W.1) (h' : m.φ ⁻¹ᵁ O ≤ t'.G.hom ⁻¹ᵁ W'.1)
      (r : Γ(X, W.1)), (m.φ.app O).hom ((t.G.hom.appLE W.1 O h).hom r) =
        (t'.G.hom.appLE W'.1 (m.φ ⁻¹ᵁ O) h').hom (ψ.hom r) := by
    intro O h h' r
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, hψ,
      Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, cong sq]
  have vpull : ∀ {A : Type} [CommRing A] (z : Sp A ⟶ t'.G.left) (U₁ : t.G.left.Opens) (U₂ : t'.G.left.Opens)
      (le : U₂ ≤ m.φ ⁻¹ᵁ U₁), ⊤ ≤ z ⁻¹ᵁ U₂ → ∀ y, valR z U₂ ((m.φ.appLE U₁ U₂ le).hom y) = valR (z ≫ m.φ) U₁ y := by
    intro A _ z U₁ U₂ le hz y
    have e : (m.φ.appLE U₁ U₂ le).hom y = resG _ le ((m.φ.app U₁).hom y) := rfl
    rw [e, GlobalTheory.CechKS.valR_resG z le hz, GlobalTheory.CechKS.valR_comp_app]
  refine ⟨e.symm.toRingHom.mapMatrix Θ', J, fun i => m.φ ''ᵁ Wc i, fun i => cp.idx (jj i), d₂, ?_, ?_, hd₂F, ?_, ?_⟩
  · rw [← Scheme.Hom.image_iSup, hsup, inf_top_eq, inf_eq_left.2 hWV, hW']
    have e1 : t'.G.hom ⁻¹ᵁ (j ⁻¹ᵁ W.1) = m.φ ⁻¹ᵁ (t.G.hom ⁻¹ᵁ W.1) := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq]
    rw [e1, Scheme.Hom.image_preimage_eq_opensRange_inf, hφr, ← Scheme.Hom.preimage_inf, inf_eq_right.2 hWr]
  · intro i y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact cp.le _ (hj i hx)
  · intro i h r
    apply (ConcreteCategory.bijective_of_isIso (m.φ.app (m.φ ''ᵁ Wc i))).1
    have hle : m.φ ⁻¹ᵁ (m.φ ''ᵁ Wc i) ≤ Wc i := (hpi i).le
    rw [hd₂ i _ le_rfl, happ _ h (hle.trans (hWc i)), happ _ h (hle.trans (hWc i)),
      ← GlobalTheory.KSRechart.resG_appLE t'.G.hom W'.1 (hWc i) hle, ← GlobalTheory.KSRechart.resG_appLE t'.G.hom W'.1 (hWc i) hle,
      (hfld i).2.2 (Wc i) _ hle le_rfl, hcomp i (hWc i), hD]
  · intro i i' O hO f S _ φS g₀ w hg₀ hO' hw
    have hOr : ∀ y ∈ O, ∃ x, m.φ.base x = y := fun y hy => by
      obtain ⟨x, -, hx⟩ := (hO hy).1
      exact ⟨x, hx⟩
    have hg₀r : Set.range g₀.base ⊆ Set.range m.φ.base := by
      rintro _ ⟨p, rfl⟩
      exact hOr _ (hO' (Set.mem_univ p))
    set g₀' := IsOpenImmersion.lift m.φ g₀ hg₀r with hg₀'def
    have hg₀'φ : g₀' ≫ m.φ = g₀ := IsOpenImmersion.lift_fac _ _ _
    let φS' : Γ(X', W'.1) →+* S := φS.comp e.symm.toRingHom
    have hφS : φS'.comp ψ.hom = φS := by
      ext r
      show φS (e.symm (ψ.hom r)) = φS r
      congr 1
      exact e.symm_apply_apply r
    have spc : spMap φS' ≫ spMap ψ.hom = spMap (φS'.comp ψ.hom) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hg₀' : g₀' ≫ t'.G.hom = spMap φS' ≫ chart W' := by
      rw [← cancel_mono j, Category.assoc, ← sq, ← Category.assoc, hg₀'φ, hg₀, Category.assoc, hx,
        ← Category.assoc, spc, hφS]
    have hw' : ∀ a, ∃ w', w' ≫ m.φ = w a ∧ IsTranslate t' φS' g₀' (v' a) w' := fun a =>
      GlobalTheory.T.tangentTranslate_lifts_semiAbelianTripleMap E H X X' t t' j m _ _ ψ.hom (chart W) (chart W') hx (v a) (v' a) (hv a) (hv't a) (hvv a) S φS'
        g₀' hg₀' (w a) (by rw [hφS, hg₀'φ]; exact hw a)
    choose w' hw'φ hw'T using hw'
    have hOi : m.φ ⁻¹ᵁ O ≤ Wc i ⊓ Wc i' :=
      le_inf ((m.φ.preimage_mono (hO.trans inf_le_left)).trans (hpi i).le)
        ((m.φ.preimage_mono (hO.trans inf_le_right)).trans (hpi i').le)
    have hO'' : ⊤ ≤ g₀' ⁻¹ᵁ (m.φ ⁻¹ᵁ O) := by
      rw [← Scheme.Hom.comp_preimage, hg₀'φ]
      exact hO'
    have key := htest i i' (m.φ ⁻¹ᵁ O) hOi ((m.φ.app O).hom f) S φS' g₀' w' hg₀' hO'' hw'T
    rw [← hg₀'φ, GlobalTheory.CechKS.valR_comp_app, map_sub, hd₂ i O (hO.trans inf_le_left),
      hd₂ i' O (hO.trans inf_le_right), key]
    have hU' : ⊤ ≤ g₀' ⁻¹ᵁ (t'.PP.L.U (jj i) ⊓ t'.PP.L.U (jj i')) :=
      hO''.trans (g₀'.preimage_mono (hOi.trans (inf_le_inf (hj i) (hj i'))))
    have hgp := GlobalTheory.T.chartPullback_lineBundle_transition_eq_appLE _ _ t'.PP.L t.PP.L m.φ cp (jj i) (jj i')
    set le₀ : t'.PP.L.U (jj i) ⊓ t'.PP.L.U (jj i') ≤ m.φ ⁻¹ᵁ (t.PP.L.U (cp.idx (jj i)) ⊓ t.PP.L.U (cp.idx (jj i'))) :=
      le_inf (inf_le_left.trans (cp.le (jj i))) (inf_le_right.trans (cp.le (jj i')))
    have hgi : ((t'.PP.L.g (jj i) (jj i'))⁻¹ : Γ(t'.G.left, _)ˣ).val =
        (m.φ.appLE _ _ le₀).hom ((t.PP.L.g (cp.idx (jj i)) (cp.idx (jj i')))⁻¹ : Γ(t.G.left, _)ˣ).val := by
      refine Units.inv_eq_of_mul_eq_one_right ?_
      rw [hgp, ← map_mul, Units.mul_inv, map_one]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hred := GlobalTheory.T.reduction_eq_basePoint E H X' t' _ _ φS' (chart W') g₀' (v' b) (w' b) hg₀' (hv't b) (hw'T b)
    have hwU : ⊤ ≤ w' b ⁻¹ᵁ (t'.PP.L.U (jj i) ⊓ t'.PP.L.U (jj i')) := GlobalTheory.CechKS.le_preimage_of_red hred hU'
    rw [hgp, hgi, vpull _ _ _ le₀ hwU, vpull _ _ _ le₀ hU', hw'φ, hg₀'φ, ← hw'φ a, ← GlobalTheory.CechKS.valR_comp_app]
    rfl

end GlobalTheory.KSInterior

namespace GlobalTheory.KSInterior

theorem exists_isKS_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (W : Y.X.affineOpens), W.1 ≤ interior Y → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, W.1)) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (chart W) (v i)) → (∀ w, IsTanAtG Y.t (chart W) w → ∃! cf : Fin n → Γ(Y.X, W.1), IsCombAtG Y.t (chart W) v cf w) → ∀ D : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1), ∃ Θ, IsKS Y.t (interior Y) W v D Θ := by
  intro E _ _ _ H Dw l Xo c Y W hW n v hv hb D
  obtain ⟨t', m, hcp⟩ := exists_sab_chartPull Y.j Y.t
  obtain ⟨m', -⟩ := GlobalTheory.ArcChartExt.exists_sab_cancel_id Y.m m
  obtain ⟨hP, hA, hK⟩ := GlobalTheory.KSObj.proper_ample_kTriv Y.oF m'
  have hWr : W.1 ≤ Y.j.opensRange := hW
  let W' : (Xo.XF c).affineOpens := ⟨Y.j ⁻¹ᵁ W.1, W.2.preimage_of_isOpenImmersion _ hWr⟩
  have hW' : W'.1 = Y.j ⁻¹ᵁ W.1 := rfl
  let ψ := Y.j.appLE W.1 W'.1 hW'.le
  have hx : chart W' ≫ Y.j = spMap ψ.hom ≫ chart W := (IsAffineOpen.SpecMap_appLE_fromSpec Y.j W.2 W'.2 hW'.le).symm
  have hbij : Function.Bijective ψ.hom := by
    have e : Y.j ''ᵁ (Y.j ⁻¹ᵁ W.1) = W.1 := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 hWr]
    have key : ψ = Y.X.presheaf.map (eqToHom e).op ≫ (Y.j.appIso (Y.j ⁻¹ᵁ W.1)).hom := by
      rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
    rw [key]
    exact ConcreteCategory.bijective_of_isIso _
  obtain ⟨v', hv'φ, hv't, hv'b⟩ := GlobalTheory.T.tangentBasis_moves_along_semiAbelianTripleMap E H _ _ Y.t t' Y.j m _ _ ψ.hom (chart W) (chart W') hx n v hv hb
  obtain ⟨D', hD'⟩ := exists_derivation_transport (RingEquiv.ofBijective ψ.hom hbij) D
  obtain ⟨Θ', hΘ'⟩ := GlobalTheory.T.exists_cech_kodairaSpencer_class_abelianTriple E H _ t' hP hA hK W' n v' hv't hv'b D'
  exact isKS_transport E H _ _ Y.t t' Y.j m hcp (interior Y) W W' hW' hbij hW hWr n v v' hv hv't hv'φ D D'
    (fun r => hD' r) Θ' hΘ'

end GlobalTheory.KSInterior
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorPolynomialDefectStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusInvariant_heatOperator_polynomial_defect : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∃ (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (w : Dd.toPre.X → Dd.toPre.X →+ R) (π π' : Dd.toPre.X → R), IsBasic Y h ∧ HasDefect Y h (fun (k : ℕ) mu α => 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) := by
  first | exact @GlobalTheory.HeatEx.exists_basic_heat_polyDefect | exact GlobalTheory.HeatEx.exists_basic_heat_polyDefect | (intros; apply GlobalTheory.HeatEx.exists_basic_heat_polyDefect <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianOfIsGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.EvenDesc

theorem isSemiAbelian_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {β : G'.left ⟶ G.left} (h : IsGrpPullback G' G f β) (hG : IsSemiAbelian G) :
    IsSemiAbelian G' := by
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  haveI := he
  exact GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback _ G hG)

theorem mono_jK (R : Type) [CommRing R] [IsDomain R] : Mono (jK R) := by
  haveI : Scheme.Spec.IsRightAdjoint := ΓSpec.adjunction.isRightAdjoint
  have : Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))).op) := inferInstance
  exact this

end GlobalTheory.Mum.EvenDesc

set_option maxHeartbeats 2000000 in
open GlobalTheory.Mum.EvenDesc in

theorem GlobalTheory.Mum.evenOn_of_trait_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R)), GlobalTheory.LN.CDvr W → Function.Injective φ → IsLocalHom φ → IsGrpPullback GW G (spMap φ) βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW → LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A.L.pull gen.hom.left).pull κ) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁] (β : G₁.left ⟶ G.left) (κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)) (P : GlobalTheory.UU.CP G₁), FinExt ρ → IsGrpPullback G₁ G (spMap ρ) β → κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β → LBIso (P.L.L.pull (pullback.fst G₁.hom (jK R'))) ((A.L.pull gen.hom.left).pull κ₁) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X], Nonempty (GlobalTheory.UU.TQ (thickObj R' (maximalIdeal R') 0 G₁) X) → EvenOn P := by
  intro R _ _ _ hR G _ _ hG A gen hgen W _ _ _ φ GW _ _ βW DW AW UW κ hW hφi hφl hGW hκ hUW R' _ _ _ ρ G₁ _ _ β κ₁ P
    hfin hG₁ hκ₁ hP X _ _ _ hTQ

  have hgi : Function.Injective
      ((algebraMap (FractionRing W) (Kb W)).comp ((algebraMap W (FractionRing W)).comp φ)) :=
    (algebraMap (FractionRing W) (Kb W)).injective.comp ((IsFractionRing.injective W (FractionRing W)).comp hφi)
  obtain ⟨e, he⟩ := GlobalTheory.Mum.TraitExt.exists_fracHom ρ hfin.2.1 hfin.2.2 _ hgi
  obtain ⟨W₁, _, _, _, iw, φ₁, -, hW₁, hiwi, -, hiwl, hφ₁i, hφ₁l, hcomm, -, -⟩ :=
    GlobalTheory.T.exists_finite_complete_trait_extension_of_base R W R' hW φ hφi hφl ρ hfin (Kb W) e he
  have hAW : AdmBase W (maximalIdeal W) := by
    haveI := hW.1; exact ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hAW₁ : AdmBase W₁ (maximalIdeal W₁) := by
    haveI := hW₁.1; exact ⟨inferInstance, inferInstance, inferInstance, hW₁.2.1⟩
  have hGW' : IsSemiAbelian GW := isSemiAbelian_of_isGrpPullback hGW hG
  have hG₁' : IsSemiAbelian G₁ := isSemiAbelian_of_isGrpPullback hG₁ hG

  obtain ⟨hL5, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨D'', hD'', A'', U'', hPu⟩ := GlobalTheory.UT.EndBaseChange.exists_pull hL5.polBaseChange h4.unifBaseChange
    h5.psiOnExists hAW hAW₁ iw hiwi (map_maximalIdeal_le iw) hGW' UW
  have hw1 : LBIso U''.LG.L
      (UW.LG.L.pull ((Iso.refl ((Over.pullback (specOf iw)).obj GW)).hom.left ≫ pullback.fst GW.hom (specOf iw))) :=
    ⟨hPu.lg.choose, hPu.lg.choose_spec.1⟩

  have hpb1 : IsGrpPullback ((Over.pullback (specOf iw)).obj GW) GW (spMap iw) (pullback.fst GW.hom (specOf iw)) :=
    isGrpPullback_pullback GW (spMap iw)
  have hsp : spMap iw ≫ spMap φ = spMap φ₁ ≫ spMap ρ := by
    rw [GlobalTheory.Mum.TraitExt.spMap_comp, GlobalTheory.Mum.TraitExt.spMap_comp, hcomm]
  have hpb2 := hpb1.comp hGW
  have hsq : (pullback.fst GW.hom (specOf iw) ≫ βW) ≫ G.hom =
      ((Over.pullback (specOf iw)).obj GW).hom ≫ spMap φ₁ ≫ spMap ρ := by
    rw [← hsp, Category.assoc, hGW.1.w, ← Category.assoc, pullback.condition]
    rfl
  obtain ⟨β'', hβ1, hβ2⟩ : ∃ β'' : ((Over.pullback (specOf iw)).obj GW).left ⟶ G₁.left,
      β'' ≫ β = pullback.fst GW.hom (specOf iw) ≫ βW ∧
        β'' ≫ G₁.hom = ((Over.pullback (specOf iw)).obj GW).hom ≫ spMap φ₁ :=
    ⟨hG₁.1.lift _ _ hsq, hG₁.1.lift_fst _ _ _, hG₁.1.lift_snd _ _ _⟩
  have hpb3 : IsGrpPullback ((Over.pullback (specOf iw)).obj GW) G₁ (spMap φ₁) β'' :=
    hG₁.cancel (hpb2.congr hsp hβ1.symm) hβ2

  have hGW₁ : IsSemiAbelian ((Over.pullback (specOf iw)).obj GW) := IsSemiAbelian.pullback _ GW hGW'
  obtain ⟨P'', hP''L, hP''E⟩ := GlobalTheory.Mum.unif_evenOn W₁ hAW₁ D'' A'' _ hGW₁ U''

  have hprop : IsProper (pullback.snd ((Over.pullback (specOf iw)).obj GW).hom (jK W₁)) := by
    have hi : IsIso U''.gen.hom.left := ((Over.forget _).mapIso U''.gen).isIso_hom
    have := A''.isAb.proper
    have hw : pullback.snd ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) = U''.gen.hom.left ≫ A''.A.hom :=
      (Over.w U''.gen.hom).symm
    rw [hw]; infer_instance

  have c1 : pullback.fst GW.hom (specOf iw) ≫ GW.hom = ((Over.pullback (specOf iw)).obj GW).hom ≫ spMap iw :=
    pullback.condition
  have c2 : pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ ((Over.pullback (specOf iw)).obj GW).hom =
      pullback.snd ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ jK W₁ := pullback.condition
  have e1 : jK W₁ ≫ spMap iw = GlobalTheory.ArcPull.genMap hiwi ≫ jK W := by
    have := GlobalTheory.ArcPull.fracMap_sq hiwi
    rwa [Category.id_comp] at this
  have e2 : jK W₁ ≫ spMap φ₁ = GlobalTheory.ArcPull.genMap hφ₁i ≫ jK R' := by
    have := GlobalTheory.ArcPull.fracMap_sq hφ₁i
    rwa [Category.id_comp] at this
  obtain ⟨kW, hkW⟩ : ∃ kW : pullback ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ⟶ pullback GW.hom (jK W),
      kW ≫ pullback.fst GW.hom (jK W) =
        pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ pullback.fst GW.hom (specOf iw) := by
    refine ⟨pullback.lift _ (pullback.snd _ _ ≫ GlobalTheory.ArcPull.genMap hiwi) ?_, pullback.lift_fst _ _ _⟩
    rw [Category.assoc, c1, ← Category.assoc, c2, Category.assoc, Category.assoc, e1]
  obtain ⟨kG, hkG⟩ : ∃ kG : pullback ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ⟶ pullback G₁.hom (jK R'),
      kG ≫ pullback.fst G₁.hom (jK R') = pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ β'' := by
    refine ⟨pullback.lift _ (pullback.snd _ _ ≫ GlobalTheory.ArcPull.genMap hφ₁i) ?_, pullback.lift_fst _ _ _⟩
    rw [Category.assoc, hβ2, ← Category.assoc, c2, Category.assoc, Category.assoc, e2]
  have hkk : kW ≫ κ = kG ≫ κ₁ := by
    haveI := mono_jK R
    apply (cancel_mono (pullback.fst G.hom (jK R))).1
    rw [Category.assoc, Category.assoc, hκ, hκ₁, ← Category.assoc, ← Category.assoc, hkW, hkG, Category.assoc,
      Category.assoc, hβ1]
  have ga : LBIso (U''.LG.L.pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁)))
      (UW.LG.L.pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ pullback.fst GW.hom (specOf iw))) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso hw1 _ (by simp)
  have gb : LBIso (UW.LG.L.pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫
      pullback.fst GW.hom (specOf iw))) ((A.L.pull gen.hom.left).pull (kW ≫ κ)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp kW hkW.symm rfl hUW
  have gc : LBIso (P.L.L.pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ β''))
      ((A.L.pull gen.hom.left).pull (kW ≫ κ)) :=
    GlobalTheory.GenSpread.lbIso_pull_comp kG hkG.symm hkk hP
  have gd : LBIso (P.L.L.pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁) ≫ β''))
      ((P.L.L.pull β'').pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁))) :=
    GlobalTheory.GenSpread.lbIso_pull_pull P.L.isLB _ rfl
  have hLg : ((A.L.pull gen.hom.left).pull (kW ≫ κ)).IsLB := pull_isLB (pull_isLB A.isLB _) _
  have hgen' : LBIso (U''.LG.L.pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁)))
      ((P.L.L.pull β'').pull (pullback.fst ((Over.pullback (specOf iw)).obj GW).hom (jK W₁))) :=
    LBIso.trans (pull_isLB U''.LG.isLB _) (pull_isLB UW.LG.isLB _) (pull_isLB (pull_isLB P.L.isLB _) _) ga
      (LBIso.trans (pull_isLB UW.LG.isLB _) hLg (pull_isLB (pull_isLB P.L.isLB _) _) gb
        (LBIso.trans hLg (pull_isLB P.L.isLB _) (pull_isLB (pull_isLB P.L.isLB _) _) gc.symm gd))

  haveI : IsNoetherianRing W₁ := hAW₁.1
  haveI : IsIntegrallyClosed W₁ := hAW₁.2.2.1
  haveI : Smooth ((Over.pullback (specOf iw)).obj GW).hom := hGW₁.smooth
  haveI : GeometricallyIntegral ((Over.pullback (specOf iw)).obj GW).hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hGW₁.smooth hGW₁.geomConnected
  have hLB : LBIso U''.LG.L (P.L.L.pull β'') :=
    GlobalTheory.Mum.lbIso_of_generic_local W₁ _ (eSec ((Over.pullback (specOf iw)).obj GW))
      (Over.w η[(Over.pullback (specOf iw)).obj GW]) _ _ U''.LG.isLB (pull_isLB P.L.isLB _) hgen'
  have hLB' : LBIso P''.L.L (P.L.L.pull β'') := by rw [hP''L]; exact hLB

  exact GlobalTheory.T.evenOnTorus_descends_along_localHom R' W₁ φ₁ hφ₁l G₁ hG₁' _ β'' hpb3 hprop P P'' hLB' hP''E X hTQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareDeRhamDualityOfHodgeDeRhamDual
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PoincareDeRhamDualityProof

theorem poincareDeRhamDuality_of_hodge (H : GlobalTheory.Published.AbelianHodgeDeRham) (D : GlobalTheory.Published.DualAbelianScheme) :
    GlobalTheory.Published.PoincareDeRhamDuality := by
  intro R _ A B _ _ g hA hB hg hg' P hP φ hφ
  exact GlobalTheory.T.deRham_pairing_perfect_and_hodge_filtration_isotropic H R A B g hA hB hg hg' P
    (GlobalTheory.Published.PoincareDeRhamDuality.Test.isPerfect_of_isDual D hA hP) φ hφ

end GlobalTheory.PoincareDeRhamDualityProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedAbelianPartFibreConjugateIsoMumfordStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedAbelianPart_fibre_conjugate_iso_mumford : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∀ (a : Q.X) (p : Sp K ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = spMap (ev.comp ρ) ≫ (Q.c a).left → p ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = 𝟙 _ → ∃ (f : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left) (f₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left), IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f ∧ IsSquare f f₂ ∧ (∀ (ψ₀ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 Q.B).left) (ψσ : (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left ⟶ (G2 Q.B).left), IsSquare (pullback.fst Q.B.hom (spMap (ev.comp ρ))) ψ₀ → IsSquare (pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) ψσ → LBIso ((abelian₂ Q.B Q.M.L).pull ψ₀) ((abelian₂ Q.B Q.M.L).pull (f₂ ≫ ψσ))) ∧ p ≫ f ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) = spMap σ.toRingHom ≫ p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) := by
  first | exact @GlobalTheory.Poinc.Sep.conj_fibre_core | exact GlobalTheory.Poinc.Sep.conj_fibre_core | (intros; apply GlobalTheory.Poinc.Sep.conj_fibre_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareCommutationIntegralIdentityStatement
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
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_commutation_integral_identity : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : GlobalTheory.ChainFr.Fr W) (A₁ : GlobalTheory.ChainFr.Fr W₁) (B : GlobalTheory.ChainFr.Fr X) (α β : (AE D)ˣ →* Circle),
    GlobalTheory.SquareComm.IsTriple W W₁ X α β →
    ∀ (ν : MeasureTheory.Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : MeasureTheory.Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)),
    GlobalTheory.SquareComm.IsHaarFD W ν 𝓕 → GlobalTheory.SquareComm.IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ GlobalTheory.SquareComm.algF ψ θ true A B, ∀ Φ' ∈ GlobalTheory.SquareComm.algF ψ θ false A₁ B,
      (∀ h, MeasureTheory.IntegrableOn (fun g => thetaKO ωB g h Φ') 𝓕₁ ν₁) → p Φ = p' Φ' →
      GlobalTheory.SquareComm.thetaInt ωA ν 𝓕 Φ = c • GlobalTheory.SquareComm.thetaInt ωB ν₁ 𝓕₁ Φ' := by
  first | exact @GlobalTheory.ThetaAgreeConv.thetaIntegralsAgree_of_integrable | exact GlobalTheory.ThetaAgreeConv.thetaIntegralsAgree_of_integrable | (intros; apply GlobalTheory.ThetaAgreeConv.thetaIntegralsAgree_of_integrable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTorusTranslatesTwistedSumsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_constants_torus_translates_twisted_sums : (∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ (sg : ℤˣ) (eps : X₁.S.Gam → X₁.S.Gam → ℕ), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → X) → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ zt h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ zt = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) → X₁.M.stalkHom z₁ h = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ eps (lab c) τ) * X₁.S.th (lab c + τ) / X₁.S.th x₀ → ∀ wt : (Fin 8 → X) → ZMod (X₁.S.r * X₁.S.N), (∀ a mu, 𝔪.YY a mu → wt mu = (sg : ℤ) • eStd X₁.S.g _ τ a) → SumI (maximalIdeal V) (fun mu => ev zt ^ (wt mu).val * T mu c) (ev h)) := by
  first | exact @GlobalTheory.Poinc.Sep.twistSum_translate | exact GlobalTheory.Poinc.Sep.twistSum_translate | (intros; apply GlobalTheory.Poinc.Sep.twistSum_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsTermsDividingGroupLabelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMember_exists_terms_dividing_group_label : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (t1 : Y1 → V1) (δ1 : I → Y1 → Y1) (𝔪1 : GlobalTheory.GSep.GMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (a : X₁.S.Gam), a ∈ X₁.S.HH X₁.M z₁ → ∃ T : Y1 → Unit → V1, 𝔪1.Terms x₀ (fun _ : Unit => a) T := by
  first | exact @GlobalTheory.GSep.exists_terms_single | exact GlobalTheory.GSep.exists_terms_single | (intros; apply GlobalTheory.GSep.exists_terms_single <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMemberExistsTermsTorusTranslateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaMember_exists_terms_torus_translate : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ T' : X → Unit → V, 𝔪.Terms x₀ (fun _ : Unit => lab c + τ) T' := by
  first | exact @GlobalTheory.GSep.TermsExt.exists_terms_translate | exact GlobalTheory.GSep.TermsExt.exists_terms_translate | (intros; apply GlobalTheory.GSep.TermsExt.exists_terms_translate <;> assumption)
end

