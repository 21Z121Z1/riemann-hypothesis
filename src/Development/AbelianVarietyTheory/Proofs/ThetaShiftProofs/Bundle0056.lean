import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingThick
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointUniqueAndBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0055
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0035
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0045
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFrameChangeIntegralInvertibleMatrix
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointEqOfModelsOverBase
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ArcQ

theorem exists_generic_lift {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {k : Type} [Field k] (bF : c.F →+* k) {O : Type} [CommRing O]
    {β : O →+* c.F} (Y : Model Xo c β) (χ : Sp (PowerSeries k) ⟶ Y.X)
    (hχ : χ ≫ Y.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp β))
    {S : Type} [CommRing S] [Nontrivial S] (ι : PowerSeries k →+* S) (hι : IsUnit (ι PowerSeries.X))
    (z : Sp S ⟶ Xo.XF c) (hz : z ≫ Y.j = spMap ι ≫ χ) :
    ∃ y : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c, y ≫ Y.j = Out.jK (PowerSeries k) ≫ χ ∧
      y ≫ pullback.snd _ _ = Out.jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF := by
  have := Y.jQ_open
  have w : (Out.jK (PowerSeries k) ≫ χ) ≫ Y.s =
      (Out.jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF) ≫ spMap β := by
    rw [Category.assoc, hχ, spMap_comp]; simp only [Category.assoc]
  obtain ⟨q⟩ : Nonempty (Sp S) := (inferInstance : Nonempty (PrimeSpectrum S))
  have hq : PowerSeries.X ∉ (spMap ι q).asIdeal := fun h =>
    q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show ι PowerSeries.X ∈ q.asIdeal from h) hι)
  obtain ⟨p₀, hp₀⟩ := mem_range_jK _ hq
  have hr : Set.range (pullback.lift _ _ w) ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = p₀ := Subsingleton.elim (α := PrimeSpectrum (FractionRing (PowerSeries k))) _ _
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, hp₀,
      ← Scheme.Hom.comp_apply, ← hz, Scheme.Hom.comp_apply]
    exact GlobalTheory.ThetaShiftProofs.j_mem_abLocus Y _
  have hy := IsOpenImmersion.lift_fac Y.jQ _ hr
  refine ⟨IsOpenImmersion.lift Y.jQ _ hr, ?_, ?_⟩
  · unfold Model.j
    rw [← Category.assoc, hy, pullback.lift_fst]
  · rw [← Y.jQ_over, ← Category.assoc, hy, pullback.lift_snd]

theorem isArcFr_eq_of_overBase : Out.Laws → Out.Laws2 → Out.Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn Dw l (RingHom.id c.F) k bF) (V V' : ValuationSubring ℂ) (Y : Model Xo c (c.V V).subtype) (Y' : Model Xo c (c.V V').subtype) (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : Wit Y (a.restrict (c.V V).subtype) χ) (W' : Wit Y' (a.restrict (c.V V').subtype) χ'), χ ≫ Y.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp (c.V V).subtype) → χ' ≫ Y'.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp (c.V V').subtype) → ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR k)) (th : a.D₀.P.L.Sec), ThNZ th → ∀ (S : Type) [CommRing S] [Algebra c.F S] [Nontrivial S] (ι : PowerSeries k →+* S) (y y' : FrPt Xo c S), IsUnit (ι PowerSeries.X) → IsArcFr W e th ι y → IsArcFr W' e th ι y' → y = y' := by
  intro h1 h2 h5 E _ _ _ H Dw l Xo c k _ bF a V V' Y Y' χ χ' W W' hχ hχ' e th hth S _ _ _ ι y y' hι hy hy'
  have hj : Mono Y.j := GlobalTheory.ThetaShiftProofs.mono_j Y (mono_spMap_subtype _)
  have hj' : Mono Y'.j := GlobalTheory.ThetaShiftProofs.mono_j Y' (mono_spMap_subtype _)
  obtain ⟨y₀, a₁, a₂⟩ := exists_generic_lift bF Y χ hχ ι hι hy.choose
    hy.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
  obtain ⟨y₀', b₁, b₂⟩ := exists_generic_lift bF Y' χ' hχ' ι hι hy'.choose
    hy'.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1
  obtain ⟨rfl, hψ⟩ := GlobalTheory.arc_rigidity_two_models_of_mono h1 h2 h5 E H Dw l Xo c k bF a _ _ _ _ Y Y' χ χ' W W' y₀ y₀' a₁ b₁ a₂ b₂
  obtain ⟨ψ, hψ⟩ := hψ hj
  have hy₁ := GlobalTheory.ArcQ.isArcFr_of_agree h1 h2 E H Dw l Xo c k bF a _ _ _ _ Y Y' χ χ' W W' ψ hψ y₀ a₁ b₁ hj e th hth S ι y hι hy
  exact (GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c _ _ Y' k _ _ χ' W' e th hth S ι y' hy').1 hj' y hy₁

end GlobalTheory.ArcQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsArcBasisBaseChange
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.IntModelExists

theorem dualMap_id (R : Type) [CommRing R] : dualMap (RingHom.id R) = RingHom.id _ :=
  RingHom.ext fun x => by ext <;> simp [dualMap]

theorem maps_self {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X) {w : LB.Iso L (L.pull F)}
    (hw : w = isoPullId (idIso L) hF) {h : Y ⟶ Y} (hh : h = 𝟙 Y) {K I : Type} [Fintype K] (φ : I → K → (Y ⟶ X))
    (ε : K → ℤ) (t : ∀ i, LB.Gen (LB.LinComb L (φ i) ε)) (ht : ∀ i, (t i).IsGen) {i i' : I} (hi : i' = i) :
    ∃ hψ : ∀ k, φ i k ≫ F = h ≫ φ i' k,
      LB.Gen.Maps (LB.linCombIso w _ ε) (t i) (Out.GeneratorPullback.pullAlong L F h _ ε _ hψ (t i')) := by
  subst hi hw hh
  have hψ : ∀ k, φ i' k ≫ F = 𝟙 Y ≫ φ i' k := fun k => by rw [hF, Category.comp_id, Category.id_comp]
  exact ⟨hψ, (maps_iff _ _ (φ i') ε (t i') (t i') (𝟙 Y) _ (Out.GeneratorPullback.pullAlong_le L F _ _ _ hψ) (fun _ => rfl)).2
    (NoTorus.pmaps_id hF _ _ (ht i'))⟩

open scoped CategoryTheory.Obj in

theorem exists_self {R : Type} [CommRing R] [IsDomain R] (D : Out.DegPre R) (h : ∀ χ, PsiUnitOn D χ Set.univ) :
    ∃ p : Out.IsPullDeg (RingHom.id R) D D, (∀ q : D.P.A.left ⟶ D.P.A.left, q ≫ prj p = prj p ≫ q) ∧
      (∀ y, p.xe y = y) ∧ ∀ ν, LetBC p ν ν := by
  have : IsMonHom (Iso.refl D.P.A).hom := inferInstanceAs (IsMonHom (𝟙 D.P.A))
  have gp : IsGrpPullback D.P.A D.P.A (Out.specOf (RingHom.id R)) (Iso.refl D.P.A).hom.left :=
    (isGrpPullback_of_iso (Iso.refl D.P.A)).congr (specOf_id R).symm rfl
  obtain ⟨e, me, hF⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (Out.specOf (RingHom.id R)))
  have hF' : e.hom.left ≫ pullback.fst D.P.A.hom (Out.specOf (RingHom.id R)) = 𝟙 _ := hF
  obtain ⟨ψW⟩ := GlobalTheory.ArcPull.nonempty_psiOn_top D h
  obtain ⟨p, h₁, h₂, h₃⟩ := UnifUniq.exists_isPullDeg_id D D ⊤ trivial ψW e me
    (isoPullId (idIso D.P.L) hF') ((isGen_iff _).2 (isoPullId_pgen (idIso_isGen D.P.isLB) hF'))
    ((congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (NoTorus.pmaps_id hF' (K := PUnit) (fun _ => eSec D.P.A) (fun _ => 1) D.rig_gen) (AddEquiv.refl _)
    (fun x => (congrArg (_ ≫ ·) hF').trans (Category.comp_id _))
    (fun x => NoTorus.pmaps_id hF' (K := PUnit) (fun _ => D.xK x) (fun _ => -1) (D.psi_gen x))
  subst h₁
  have hx : ∀ y, p.xe y = y := fun y => by rw [h₃]; rfl
  have hp : prj p = 𝟙 _ := hF'
  have hs : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
    rw [dualMap_id]; exact Spec.map_id (CommRingCat.of (DualNumber R))
  refine ⟨p, fun q => by rw [hp, Category.comp_id, Category.id_comp], hx, fun ν => ⟨?_, fun χ => ?_⟩⟩
  · exact ((congrArg (_ ≫ ·) hF').trans (Category.comp_id _)).trans
      ((congrArg (· ≫ ν.b.left) hs).trans (Category.id_comp _)).symm
  · exact maps_self hF' (eq_of_heq h₂) hs (Out.DegPre.gtφT D (epsR R) ν.b) _ ν.s ν.isGen (hx χ)

theorem isLieComb_trans {S : Type} [CommRing S] [IsLocalRing S] {G : Over (Sp S)} [GrpObj G] [Smooth G.hom] {d n : ℕ}
    {v : Fin d → (epsR S ⟶ G)} {u : Fin n → (epsR S ⟶ G)} {w : epsR S ⟶ G} (hv : ∀ i, IsTangent (v i))
    (hu : ∀ i, IsTangent (u i)) (hw : IsTangent w) {U : Fin n → Fin d → S} (hU : ∀ i, IsLieComb (U i) v (u i))
    {a : Fin n → S} (ha : IsLieComb a u w) : IsLieComb (fun j => ∑ i, a i * U i j) v w := by
  obtain ⟨m, y, hy⟩ := Chart.univChartLoc G
  have tv := fun i => (Chart.isTan_iff _).2 (hv i)
  have tu := fun i => (Chart.isTan_iff _).2 (hu i)
  have tw := (Chart.isTan_iff _).2 hw
  rw [Chart.comb_iff_coord hy _ tv tw, (Chart.comb_iff_coord hy _ tu tw).1 ha]
  simp only [(Chart.comb_iff_coord hy _ tv (tu _)).1 (hU _), Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem isLieComb_single {S : Type} [CommRing S] [IsLocalRing S] {G : Over (Sp S)} [GrpObj G] [Smooth G.hom] {d : ℕ}
    {v : Fin d → (epsR S ⟶ G)} (hv : ∀ i, IsTangent (v i)) (j : Fin d) : IsLieComb (Pi.single j 1) v (v j) := by
  obtain ⟨m, y, hy⟩ := Chart.univChartLoc G
  have tv := fun i => (Chart.isTan_iff _).2 (hv i)
  rw [Chart.comb_iff_coord hy _ tv (tv j)]
  simp [Pi.single_apply]

theorem flat_of_injective {A B : Type} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A] [CommRing B] [IsDomain B]
    (f : A →+* B) (hf : Function.Injective f) : f.Flat := by
  algebraize [f]
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 hf
  show Module.Flat A B
  infer_instance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem exists_matrix (hG : Out.GlobalFnsSt) {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    {b : O →+* A} {a : ArcIn Dw l β A b} {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)
    {ρ : (E →+* ℂ) → (𝓞 E →+* A)} {e₁ e₂ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)}
    (h₁ : ArcBasis W ρ e₁) (h₂ : ArcBasis W ρ e₂) :
    ∃ g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A,
      (∀ τ, (g τ).det ≠ 0) ∧ ∀ τ k, GtComb (g τ k) (e₁ τ) (e₂ τ k) := by
  have key := (GlobalTheory.T.constantEigenbasis_independent_of_witness hG E H Dw l Xo c O β Y A b a χ W ρ e₁ h₁).2.2
  obtain ⟨v₁, i₁, b₁⟩ := h₁
  obtain ⟨v₂, i₂, b₂⟩ := h₂
  choose g hg using fun τ k => (key τ (e₂ τ k) (v₂ τ k)
    (((GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c O β Y A b a χ W (e₂ τ k)).2 _ (i₂ τ k)).2 ((b₂ τ).1 k).1) (i₂ τ k)
    ((b₂ τ).1 k).2).exists
  refine ⟨fun τ => Matrix.of (g τ), fun τ => ?_, hg⟩
  have := W.t.semi.smooth
  have hU : ∀ k, IsLieComb (fun i => PowerSeries.C (R := A) (g τ k i)) (v₁ τ) (v₂ τ k) := fun k =>
    (GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y A b a χ W _ (g τ k) (e₁ τ) (e₂ τ k) (v₁ τ) (v₂ τ k) (i₁ τ) (hg τ k)).1 (i₂ τ k)
  choose h hh using fun j => ((b₂ τ).2 (v₁ τ j) ((b₁ τ).1 j).1 ((b₁ τ).1 j).2).exists
  have hm : Matrix.of h * (PowerSeries.C (R := A)).mapMatrix (Matrix.of (g τ)) = 1 := by
    ext1 j k
    have := congrFun (((b₁ τ).2 (v₁ τ j) ((b₁ τ).1 j).1 ((b₁ τ).1 j).2).unique
      (isLieComb_trans (fun i => ((b₁ τ).1 i).1) (fun i => ((b₂ τ).1 i).1) ((b₁ τ).1 j).1 hU (hh j))
      (isLieComb_single (fun i => ((b₁ τ).1 i).1) j)) k
    simpa [Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, eq_comm] using this
  intro h0
  have := congrArg Matrix.det hm
  rw [Matrix.det_mul, ← RingHom.map_det, h0, map_zero, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

theorem exists_arcBasis_baseChange (hL : Out.Laws) (hL₂ : Out.Laws2) (hU : Out.UnifBaseChangeSt) (hL₅ : Out.Laws5)
    {A A' : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsPrincipalIdealRing A]
    [CommRing A'] [IsDomain A'] [IsLocalRing A'] [IsPrincipalIdealRing A'] {b : O →+* A} {b' : O →+* A'}
    {a : ArcIn Dw l β A b} {a' : ArcIn Dw l β A' b'} {f : A →+* A'} (hf : Function.Injective f)
    {p : Out.IsPullDeg f a.D₀ a'.D₀} (hp : InBC f a a' p) {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)
    {ρ : (E →+* ℂ) → (𝓞 E →+* A)} {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)}
    (h : ArcBasis W ρ e) :
    ∃ (W' : Wit Y a' (spMap (PowerSeries.map f) ≫ χ))
      (e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a'.D₀ (epsR A')),
      (∀ τ k, LetBC p (e τ k) (e' τ k)) ∧ ArcBasis W' (fun τ => f.comp (ρ τ)) e' := by
  obtain ⟨hW, hν, -⟩ := (GlobalTheory.T.degenerationData_baseChanges_exist_pid hL hL₂ hU hL₅ E H Dw l Xo c O β Y A A' b a f hf b' hp.1).2 a' p hp
  obtain ⟨W', hW'⟩ := hW χ W
  choose e' he' using fun τ k => (hν (e τ k)).exists
  obtain ⟨m, -, hm, -⟩ := GlobalTheory.T.tangentVectors_thetaSection_arcWitness_baseChange hL hL₂ E H Dw l Xo c O β Y A b a χ W A' b' a' f p W' hp hW'
  have hfl : ((PowerSeries.map f).comp (PowerSeries.C (R := A))).Flat := by
    refine flat_of_injective _ fun x y hxy => hf (PowerSeries.C_injective ?_)
    simpa using hxy
  obtain ⟨u, hu, hb⟩ := GlobalTheory.T.constant_arc_eigenbasis_flat_baseChange hL.globalFns E H Dw l Xo c O β Y A b a χ W ρ e h (PowerSeries A')
    (PowerSeries.map f) hfl W'.t m
  refine ⟨W', e', he', u, fun τ k => ?_, fun τ => ?_⟩
  · obtain ⟨v, hv, huv⟩ := hu τ k
    exact hm _ _ v _ (he' τ k) hv huv
  · simpa only [PowerSeries.map_C, RingHom.comp_apply] using hb τ

theorem mem_of_isIntegral {F : Type} [Field F] (V : ValuationSubring F) {x : F} (h : IsIntegral ℤ x) : x ∈ V := by
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := F)).1 h.tower_top
  exact hy ▸ y.2

theorem exists_values (c : Coeff l) (W : ValuationSubring ℂ) :
    ∃ r z : c.V W, (((c.V W).subtype r : c.F) : ℂ) = H.rt0 ∧ (((c.V W).subtype z : c.F) : ℂ) = zeta l.A := by
  have key : ∀ (x : c.F) (n : ℕ), 0 < n → ∀ m : ℤ, x ^ n = m → x ∈ c.V W := fun x n hn m h =>
    mem_of_isIntegral _ (IsIntegral.of_pow hn (by
      rw [h]; simpa using isIntegral_algebraMap (R := ℤ) (A := c.F) (x := m)))
  refine ⟨⟨⟨_, GlobalTheory.HostModel.sqrtNegDisc_mem_coeffField c⟩, key _ 2 two_pos (-(H.d : ℤ)) ?_⟩,
    ⟨⟨_, GlobalTheory.HostModel.zeta_A_mem_coeff c⟩, key _ l.A l.A_pos 1 ?_⟩, rfl, rfl⟩
  · apply Subtype.ext
    simpa using H.sqrt_neg_disc_sq
  · apply Subtype.ext
    simpa [zeta] using (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one

def embV (c : Coeff l) (W : ValuationSubring ℂ) (τ : E →+* ℂ) : 𝓞 E →+* c.V W :=
  (embK c τ).codRestrict (c.V W).toSubring fun x =>
    mem_of_isIntegral _ ((RingOfIntegers.isIntegral x).map (embK c τ).toIntAlgHom)

end GlobalTheory.IntModelExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicDegenerationArcOfUniformisationStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_degenerationArc_of_uniformisation : ReciprocityTheory.ChartRestriction.G.Out.Laws → ReciprocityTheory.ChartRestriction.G.Out.Laws2 → ReciprocityTheory.ChartRestriction.G.Geo.Tor.ThetaUnifAV → ReciprocityTheory.ChartRestriction.G.Geo.Tor.ToroidalArchimedeanCondition := by
  first | exact @GlobalTheory.HolomorphicArc.main | exact GlobalTheory.HolomorphicArc.main | (intros; apply GlobalTheory.HolomorphicArc.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IntegralOfFrChg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

noncomputable section

namespace GlobalTheory.ArcQ.IntChg

section Sec

variable {X Y : Scheme.{0}}

def mulSec {L : LB X} (r : Γ(X, ⊤)) (s : LB.Sec L) : LB.Sec L where
  f i := resG X le_top r * s.f i
  compat i j := by
    have e : ∀ (U : X.Opens) (h : L.U i ⊓ L.U j ≤ U),
        (X.presheaf.map (homOfLE h).op).hom (resG X (le_top : U ≤ ⊤) r) = resG X le_top r := fun U h => by
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
    rw [map_mul, map_mul, s.compat i j, e, e, mul_left_comm]

theorem res_res {U V : X.Opens} (h : V ≤ U) (r : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom (resG X (le_top : U ≤ ⊤) r) = resG X le_top r := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem appLE_res (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) (r : Γ(X, ⊤)) :
    (f.appLE U V h).hom (resG X le_top r) = resG Y le_top (f.appTop.hom r) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rfl

theorem isoMaps_mul {L M : LB X} {w : LB.Iso L M} {s : LB.Sec L} {s' : LB.Sec M} (h : IsoMaps w s s')
    (r : Γ(X, ⊤)) : IsoMaps w (mulSec r s) (mulSec r s') := by
  intro i k
  have := h i k
  simp only [mulSec, map_mul, res_res]
  rw [this, mul_left_comm]

theorem pullSec_mul {L : LB X} {f : Y ⟶ X} {s : LB.Sec L} {s' : LB.Sec (L.pull f)} (h : PullSec f s s')
    (r : Γ(X, ⊤)) : PullSec f (mulSec r s) (mulSec (f.appTop.hom r) s') := by
  intro j hj
  simp only [mulSec, map_mul, appLE_res]
  rw [h j hj]

theorem appTop_toΓ {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (a : A) :
    (spMap φ).appTop.hom (toΓ A a) = toΓ B (φ a) := by
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  exact this.symm

end Sec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem integral_scal (T : CDVR) (io : c.F →+* T.Fr) : letI := io.toAlgebra
    ∀ (y : FrPt Xo c T.Fr) (a : T.Vˣ) (s' : LB.Sec (PPx y.x))
      (hg : ∀ s'' : LB.Sec (PPx y.x), ∃! b : T.Fr, ∀ i, s''.f i = scal y.x b i * s'.f i),
      (∀ i, s'.f i = scal y.x (algebraMap T.V T.Fr a) i * y.s.f i) → Integral T io y →
      Integral T io { y with s := s', gen := hg } := by
  let _ := io.toAlgebra
  intro y a s' hg hs h
  obtain ⟨G, t', m1, m2, hu, θ, hθ, w1, w2, σ, s1, θ2, r1, r2, i1, i2, hp, hl⟩ := h
  have hc : m2.φ.appTop.hom (G.G.hom.appTop.hom (toΓ T.V a)) =
      t'.G.hom.appTop.hom (toΓ T.Fr (algebraMap T.V T.Fr a)) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, m2.cart.1.w, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply]
    exact congrArg _ (appTop_toΓ _ _)
  refine ⟨G, t', m1, m2, hu, mulSec (G.G.hom.appTop.hom (toΓ T.V a)) θ, fun τ => ?_, w1, w2, _, _, _, r1, r2,
    isoMaps_mul i1 _, isoMaps_mul i2 _, pullSec_mul hp _, ?_⟩
  · obtain ⟨b, hb, hbu⟩ := hθ τ
    have key : ∀ (d : T.V) i, resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V d)) *
        (mulSec (G.G.hom.appTop.hom (toΓ T.V a)) θ).f i =
        resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V (d * a))) * θ.f i := fun d i => by
      simp only [mulSec, map_mul, _root_.mul_assoc]
    refine ⟨b * ↑a⁻¹, fun i => ?_, fun d hd => ?_⟩
    · rw [key, Units.inv_mul_cancel_right]; exact hb i
    · rw [← hbu (d * a) fun i => by rw [← key]; exact hd i, Units.mul_inv_cancel_right]
  · intro g e1 e2 j hj
    have e3 := hl g e1 e2 j hj
    show resG _ le_top _ * s1.f j = (g.appLE _ _ hj).hom (s'.f _)
    refine Eq.symm ((congrArg _ (hs _)).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ e3.symm)))
    refine (appLE_res g _ _ hj _).trans (congrArg _ ?_)
    rw [hc, ← e2, Scheme.Hom.comp_appTop]
    rfl

theorem integral_chg (T : CDVR) (io : c.F →+* T.Fr) : letI := io.toAlgebra
    ∀ (y y' : FrPt Xo c T.Fr) (k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V) (a : T.Vˣ),
      (∀ τ, IsUnit (k τ).det) → FrChg (fun τ => (k τ).map (algebraMap T.V T.Fr)) (algebraMap T.V T.Fr a) y y' →
      Integral T io y → Integral T io y' := by
  let _ := io.toAlgebra
  intro y y' k a hk ⟨hx, hu, pm, h1, h2, h3⟩ hy
  have hk' : ∀ τ, IsUnit (k τ).transpose.det := fun τ => by rw [Matrix.det_transpose]; exact hk τ
  have hK : ∀ τ, IsUnit ((k τ).transpose.map (algebraMap T.V T.Fr)).det := fun τ => by
    have e : ((k τ).transpose.map (algebraMap T.V T.Fr)).det = algebraMap T.V T.Fr (k τ).transpose.det :=
      (RingHom.map_det _ _).symm
    rw [e]
    exact (hk' τ).map _
  have hr := GlobalTheory.IntRebase.integral_reb T io y hy (fun τ => (k τ).transpose) hk' hK
  obtain ⟨zx, zo, zu, zt, ze, zb, zs, zg⟩ := y'
  simp only at hx
  subst hx
  have eu : zu = (GlobalTheory.IntRebase.rebase₂ y _ hK).u := by
    funext τ i
    exact Formalism.L2.PjFree.isCombAt_unique (hu τ i)
      ((GlobalTheory.IntRebase.isCombAtG_iff Xo.univ.t y.x (fun j => GlobalTheory.IntRebase.ovT (t := Xo.univ.t) (y.tan τ j)) _ _).2 rfl)
  subst eu
  have ep : pm = 𝟙 _ := by
    apply pullback.hom_ext
    · refine h2.trans ?_
      simp only [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id, Category.id_comp]
      rfl
    · exact h1.trans (Category.id_comp _).symm
  subst ep
  refine integral_scal T io (GlobalTheory.IntRebase.rebase₂ y _ hK) a zs zg (fun i => ?_) hr
  exact (h3 i le_rfl).symm.trans (GlobalTheory.IntRebase.id_appLE_apply _ _ _ _)

theorem integral_of_frChg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V) (s : T.V), (∀ τ, IsUnit (g τ).det) → IsUnit s → letI := io.toAlgebra; ∀ y y' : FrPt Xo c T.Fr, FrChg (fun τ => (g τ).map (algebraMap T.V T.Fr)) (algebraMap T.V T.Fr s) y y' → Integral T io y → Integral T io y' := by
  intro E _ _ _ H Dw l Xo c T io g s hg hs y y' h hy
  obtain ⟨a, rfl⟩ := hs
  exact integral_chg T io y y' g a hg h hy

end GlobalTheory.ArcQ.IntChg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsFramedPointOfArcBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFramedPoint_of_arc_baseChange : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (A' : Type) [CommRing A'] [IsDomain A'] [IsLocalRing A'] [IsNoetherianRing A'] (b' : O →+* A') (a' : ArcIn Dw l β A' b') (f : A →+* A') (p : Out.IsPullDeg f a.D₀ a'.D₀) (W' : Wit Y a' (spMap (PowerSeries.map f) ≫ χ)), Mono Y.j → InBC f a a' p → WitBC f p W W' → ∀ (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)) (e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a'.D₀ (epsR A')) th th', (∀ τ k, LetBC p (e τ k) (e' τ k)) → ThBC p th th' → ∀ (S : Type) [CommRing S] [Algebra c.F S] (ι' : PowerSeries A' →+* S) (y : FrPt Xo c S), IsArcFr W e th (ι'.comp (PowerSeries.map f)) y → IsArcFr W' e' th' ι' y := by
  first | exact @GlobalTheory.ArcQ.isArcFr_witBC | exact GlobalTheory.ArcQ.isArcFr_witBC | (intros; apply GlobalTheory.ArcQ.isArcFr_witBC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaximalCuspsNoLowCoefficientIffFourierJacobiStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.ArcCM GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximalCusps_noLowCoefficient_iff_fourierJacobi : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → ∀ (ka : WeightFamilies.Wt D j) (CR Tt cc : ℝ), TieMaxCuspSt h j CR Tt cc ka := by
  first | exact @GlobalTheory.MaxCuspRecord.tieMaxCusp | exact GlobalTheory.MaxCuspRecord.tieMaxCusp | (intros; apply GlobalTheory.MaxCuspRecord.tieMaxCusp <;> assumption)
end

