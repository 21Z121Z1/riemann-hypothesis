import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifConjA
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0148
import Development.WeilBound.CoreStatements.VolumeEquality.Bundle0002
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.WeilBound.CoreStatements.VolumeEquality.LocInjA
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0150

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifConj
section
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem vecAt_conj {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K]
    {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) {n g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]
    (R R' : (Fin n → ℂ) → RiemLat E g Λ) (z : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)) (t₀ : Fin n → ℂ)
    (hR : ∀ t, (∀ x, (R' t).P x = star ((R (star t)).P x)) ∧ (R' t).Hm = (R (star t)).Hm.map (starRingEnd ℂ) ∧
      ∀ a x, (R' t).B a x = star ((R (star t)).B a (star x)))
    (h : VecAt 𝔐 R (fun t => spMap (starRingEnd ℂ) ≫ z (star t)) (star t₀)) : VecAt 𝔐 R' z t₀ := by
  intro m s hs
  obtain ⟨x, hx, hev⟩ := h m s fun a => by
    obtain ⟨v, hv⟩ := hs a
    show ∃ v, 𝔐.M.ValAt (spMap (starRingEnd ℂ) ≫ z (star (star t₀))) (s a) v
    rw [star_star]
    exact ⟨_, Cj.valAt_conj 𝔐.M _ _ v hv⟩
  refine ⟨fun a t => star (x a (star t)), fun a => Cj.analyticAt_star_star (hx a), ?_⟩
  filter_upwards [(continuous_star.continuousAt (x := t₀)).tendsto.eventually hev] with t ht
  obtain ⟨v, hv, hF⟩ := ht
  have key : ∀ (w w' : Sp ℂ ⟶ 𝔐.X) (v : Fin m → (epsAt w ⟶ 𝔐.t.G)), w' = spMap (starRingEnd ℂ) ≫ w →
      (∀ a, 𝔐.M.ValAt w (s a) (v a)) → FibreLatVec 𝔐.t w (R (star t)) (fun a => x a (star t)) v →
      ∃ v' : Fin m → (epsAt w' ⟶ 𝔐.t.G), (∀ a, 𝔐.M.ValAt w' (s a) (v' a)) ∧
        FibreLatVec 𝔐.t w' (R' t) (fun a => star (x a (star t))) v' := by
    rintro w _ v rfl hv hF
    exact ⟨fun a => Cj.cjVec w (v a), fun a => Cj.valAt_conj 𝔐.M w _ _ (hv a),
      Cj.fibreLatVec_conj 𝔐.t w _ _ _ v (hR t).1 (hR t).2.1 (hR t).2.2 (fun a => (hv a).isTanAt) hF⟩
  exact key _ _ v (by rw [Cj.cj_cj, star_star]) hv hF

theorem kUnifConj : KUnifConj := by
  rintro E _ _ _ H D l Xo c Y sm j j' n g q κ ⟨U⟩
  choose F' hq hσ hform hR using fun k => GlobalTheory.T.conjugate_universal_family E (CMType H) j j' n g (U.Di k).La (U.F k)
  have hcanc : ∀ {X : Scheme.{0}} {a b : Sp ℂ ⟶ X}, spMap (starRingEnd ℂ) ≫ a = spMap (starRingEnd ℂ) ≫ b → a = b :=
    fun {X a b} e => by rw [← Cj.cj_cj a, e, Cj.cj_cj]
  have hs : spMap (((starRingEnd ℂ).comp κ).comp (algebraMap (𝓞 c.F) c.F)) =
      spMap (starRingEnd ℂ) ≫ spMap (κ.comp (algebraMap (𝓞 c.F) c.F)) :=
    Spec.map_comp (CommRingCat.ofHom (κ.comp (algebraMap (𝓞 c.F) c.F))) (CommRingCat.ofHom (starRingEnd ℂ))
  refine ⟨{
    ι := U.ι
    fin := U.fin
    Di := U.Di
    sig := U.sig
    F := F'
    q_eq := fun k => (hq k).trans (U.q_eq k)
    form_eq := fun k => ?_
    σ_eq := fun k τ => ?_
    Γ := U.Γ
    mem_Γ := U.mem_Γ
    arith := fun k => ?_
    pt := fun k t => spMap (starRingEnd ℂ) ≫ U.pt k (star t)
    hol := fun k => ?_
    comp_s_eq_spMap_of_isOver := fun k t ht => ?_
    interior := fun k t ht => ?_
    disj := fun k k' t ht t' ht' e =>
      U.disj k k' _ (Cj.star_mem_ballDom ht) _ (Cj.star_mem_ballDom ht') (hcanc e)
    fibre := fun k t ht t' ht' => ?_
    onto := fun p hp hps => ?_
    lat := fun k t ht => ?_
    vec := fun S Ω _ K _ J _ y 𝔐 k V z hV hVs hz hzf t₀ ht₀ => ?_
    locc := fun m T y hT hTc hy hyi hys b hb b' hb' k k' t ht t' ht' e e' => ?_ }⟩
  · rw [hform]
    rcases U.form_eq k with h | h <;> rw [h]
    · exact Or.inr rfl
    · exact Or.inl (neg_neg _)
  · rw [hσ, U.σ_eq]
    rfl
  · have h := U.arith k
    unfold UnivFam.IsArith at h ⊢
    rwa [hform, Cj.autGrp_neg]
  · have h := GlobalTheory.T.holomorphic_family_conjugate _ _ _ _ (U.hol k)
    rwa [Cj.preimage_star_ballDom] at h
  · rw [Category.assoc, U.comp_s_eq_spMap_of_isOver k _ (Cj.star_mem_ballDom ht), hs]
  · rw [Cj.centre_conj]
    exact U.interior k _ (Cj.star_mem_ballDom ht)
  · have h := U.fibre k _ (Cj.star_mem_ballDom ht) _ (Cj.star_mem_ballDom ht')
    constructor
    · intro e
      obtain ⟨γ, hγ, he⟩ := h.1 (hcanc e)
      exact ⟨γ, hγ, Cj.eqvBy_conj (hR k t).1 (hR k t').1 he⟩
    · rintro ⟨γ, hγ, he⟩
      have e := h.2 ⟨γ, hγ, Cj.eqvBy_conj (fun x => by rw [(hR k t).1, star_star])
        (fun x => by rw [(hR k t').1, star_star]) he⟩
      show spMap (starRingEnd ℂ) ≫ U.pt k (star t) = spMap (starRingEnd ℂ) ≫ U.pt k (star t')
      rw [e]
  · obtain ⟨k, t, ht, e⟩ := U.onto (spMap (starRingEnd ℂ) ≫ p) (by rwa [Cj.centre_conj])
      (by rw [Category.assoc, hps, hs, Cj.cj_cj])
    refine ⟨k, star t, Cj.star_mem_ballDom ht, ?_⟩
    show spMap (starRingEnd ℂ) ≫ U.pt k (star (star t)) = p
    rw [star_star, e, Cj.cj_cj]
  · have h := Cj.fibreLatVec_conj Y.t _ _ ((F' k).R t) _ _ (hR k t).1 (hR k t).2.1 (hR k t).2.2 (fun a => a.elim)
      (U.lat k _ (Cj.star_mem_ballDom ht))
    obtain ⟨A, i, φ, u, χ, h1, h2, h3, h4, h5, -⟩ := h
    exact ⟨A, i, φ, u, χ, h1, h2, h3, h4, h5, fun a => a.elim⟩
  · refine vecAt_conj 𝔐 (U.F k).R (F' k).R z t₀ (hR k) ?_
    refine U.vec S Ω K J y 𝔐 k (star ⁻¹' V) _ (hV.preimage continuous_star) (fun t ht => ?_)
      (GlobalTheory.T.holomorphic_family_conjugate _ _ _ _ hz) (fun t ht => ?_) _ (by simpa using ht₀)
    · simpa using Cj.star_mem_ballDom (hVs ht)
    · rw [Category.assoc, hzf _ ht, Cj.cj_cj, star_star]
  · have hpre : IsPreconnected (star ⁻¹' T : Set (Fin m → ℂ)) := by
      have e₀ : (star ⁻¹' T : Set (Fin m → ℂ)) = star '' T := by
        ext x
        constructor
        · intro h
          exact ⟨star x, h, star_star x⟩
        · rintro ⟨a, ha, rfl⟩
          show star (star a) ∈ T
          rwa [star_star]
      rw [e₀]
      exact hTc.image _ continuous_star.continuousOn
    refine U.locc m (star ⁻¹' T) _ (hT.preimage continuous_star) hpre (GlobalTheory.T.holomorphic_family_conjugate _ _ _ _ hy) (fun a ha => ?_)
      (fun a ha => ?_) (star b) (by simpa using hb) (star b') (by simpa using hb') k k' _ (Cj.star_mem_ballDom ht) _
      (Cj.star_mem_ballDom ht') ?_ ?_
    · rw [Cj.centre_conj]
      exact hyi _ ha
    · rw [Category.assoc, hys _ ha, hs, Cj.cj_cj]
    · show spMap (starRingEnd ℂ) ≫ y (star (star b)) = _
      rw [star_star, e, Cj.cj_cj]
    · show spMap (starRingEnd ℂ) ≫ y (star (star b')) = _
      rw [star_star, e', Cj.cj_cj]

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifEx2
section
noncomputable section

namespace SheetDecomposition

open AlgebraicGeometry CategoryTheory NumberField MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H} {Xo : Moduli D l}
  {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {sm : CMType H → CMType H ⊕ CMType H} {j j' n : ℕ}

def BaseUnif.Locc (B : BaseUnif Y sm j j' n) : Prop :=
  ∀ (m : ℕ) (T : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Y.X)), IsOpen T → IsPreconnected T → IsHolTo T y →
    (∀ b ∈ T, centre (y b) ∈ abLocus Y.t.G) → ∀ b ∈ T, ∀ b' ∈ T, ∀ k k', ∀ t ∈ GlobalTheory.CompanionTheory.Ar.Cusp.ballDom (B.F k).q,
      ∀ t' ∈ GlobalTheory.CompanionTheory.Ar.Cusp.ballDom (B.F k').q, y b = B.pt k t → y b' = B.pt k' t' → k = k'

end

def BaseUnifEx2 : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H) (j j' n : ℕ), 1 ≤ D.p + D.q →
    (sm = Sum.inr ∧ j = D.p ∧ j' = D.q ∨ sm = Sum.inl ∧ j = D.q ∧ j' = D.p) → n = Fintype.card (CMType H) * j * j' →
    ∃ B : BaseUnif Y sm j j' n, B.Locc

def OnePiece : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l)
    (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (sm : CMType H → CMType H ⊕ CMType H) (j j' n : ℕ)
    (B : BaseUnif Y sm j j' n) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Sp Ω₀ ⟶ Y.X) (Ω₁ Ω₂ : Type) [Field Ω₁] [Field Ω₂] (ξ₁ : Sp Ω₁ ⟶ Y.X)
    (g : Ω₁ →+* Ω₂) (cst : c.F →+* Ω₂) (U : Y.X.Opens), B.Locc → IsCptGen ξ₀ → genPt ξ₁ = genPt ξ₀ →
    spMap g ≫ ξ₁ ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) → (∀ a : Ω₁, IsAlgebraic ℤ a → g a ∈ cst.range) →
    genPt ξ₀ ∈ U → (∀ p : Sp ℂ ⟶ Y.X, ⊤ ≤ p ⁻¹ᵁ U → genPt ξ₀ ⤳ centre p) →
    ∀ κ : c.F →+* ℂ, ∃! k, B.κ k = κ ∧ ∃ t ∈ GlobalTheory.CompanionTheory.Ar.Cusp.ballDom (B.F k).q, ⊤ ≤ B.pt k t ⁻¹ᵁ U

def BallVolEq : Prop :=
  Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (l : Tor.Level H)
    (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (n : ℕ) (B : BaseUnif Y Sum.inr D.p D.q n)
    (FF : Fin B.np → Set (Fin n → ℂ)), 1 ≤ D.q → 3 * D.q + 1 ≤ D.p + D.q → (∀ k, (B.F k).IsFundSet (B.Γ k) (FF k)) →
    ∀ k k', ∫ t in FF k, ballDens (B.F k).q t = ∫ t in FF k', ballDens (B.F k').q t

def DegPush : Prop :=
  ∃ c₀ : ℕ → ℕ → ℕ → ℝ, (∀ f p q, c₀ f p q ≠ 0) ∧ (PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H)
      (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F))
      [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem),
      Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → D.q ≤ D.p → ∀ (a : T.Comp) (K : Type) [Fintype K]
      (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)]
      [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (Or : CptOrigin Y T.bad Dc Hd),
      Or.bg = Sum.inl → Or.sm = Sum.inr → Or.𝔐.OmVB → Or.Good → Dc.S = ∅ → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf →
      degMu Hd = c₀ (Fintype.card (CMType H)) D.p D.q * Or.deg * Module.finrank ℚ c.F * T.vol a)

end SheetDecomposition
end
end

-- bundled from Development.WeilBound.CoreStatements.VolumeEquality.LocInj
section
noncomputable section

namespace SheetDecomposition

open NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem InLevel.congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Tor.Level H} {D : Datum H}
    {γ : D.La ≃ₗ[𝓞 E] D.La} (h : InLevel l D γ) (v : D.La) : ∃ e, γ v = v + l.M • e := by
  obtain ⟨hf, h1, -⟩ := h
  have hM : (l.M : ℤ) ≠ 0 := by
    have := l.three_le
    omega
  have key : ∀ c ∈ l.Mb, ∃ e, γ (c • v) = c • v + l.M • e := fun c hc => by
    have hd : ∀ y, (l.M : ℤ) ∣ D.EF (γ (c • v) - c • v) y := fun y => by
      obtain ⟨e, he⟩ := h1 (H.bar c • γ.symm y)
        (Submodule.smul_mem_smul (Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hc) Submodule.mem_top)
      rw [map_smul, γ.apply_symm_apply] at he
      have e1 : D.EF (γ (c • v)) y = D.EF v (H.bar c • γ.symm y) := by
        rw [← D.adj, ← hf (c • v), γ.apply_symm_apply]
      rw [map_sub, LinearMap.sub_apply, e1, D.adj, he, map_add, map_nsmul]
      exact ⟨-D.EF v e, by simp⟩
    choose φ hφ using hd
    let ψ : D.La →ₗ[ℤ] ℤ := (AddMonoidHom.mk' φ fun y y' => by
      apply mul_left_cancel₀ hM
      rw [mul_add, ← hφ, ← hφ, ← hφ, map_add]).toIntLinearMap
    obtain ⟨e, he⟩ := D.unimod.2 ψ
    refine ⟨e, sub_eq_iff_eq_add'.1 (D.unimod.1 ?_)⟩
    ext y
    rw [hφ, map_nsmul, he]
    simp [ψ]
  have : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := l.coprime ▸ Submodule.mem_top
  obtain ⟨c, hc, c', hc', e1⟩ := Submodule.mem_sup.1 this
  obtain ⟨e, he⟩ := key c hc
  obtain ⟨e', he'⟩ := h1 (c' • v) (Submodule.smul_mem_smul hc' Submodule.mem_top)
  have hv : v = c • v + c' • v := by rw [← add_smul, e1, one_smul]
  refine ⟨e + e', ?_⟩
  calc γ v = γ (c • v) + γ (c' • v) := by rw [← map_add, ← hv]
    _ = (c • v + c' • v) + l.M • (e + e') := by rw [he, he', smul_add]; abel
    _ = _ := by rw [← hv]

theorem locInj : LocInj := by
  intro E _ _ _ H l D Ψ _ j j' n g F Γ hF hΓ t₀ ht₀
  have hO : IsOpen (ballDom F.q) := BallInverse.isOpen_ballDom F.q
  let R : ↥(ballDom F.q) → RiemLat E g D.La := fun t => F.R t.1
  have hP : ∀ v, Continuous fun x => (R x).P v := fun v =>
    continuousOn_iff_continuous_restrict.1 (F.hol.2 v).continuousOn
  have hH : Continuous fun x => (R x).Hm :=
    HmCont.continuous_Hm E g D.La _ R F.form (fun x => F.form_eq _) hP
  have h := near_trivial R hP hH ⟨t₀, ht₀⟩ l.M l.three_le
  rw [nhds_prod_eq] at h
  obtain ⟨A, hA, hA'⟩ := (eventually_prod_self_iff (r := fun x y => ∀ γ : D.La ≃ₗ[𝓞 E] D.La,
    (∀ v, ∃ e, γ v = v + l.M • e) → (∀ u v, reForm (R y) (γ u) (γ v) = reForm (R x) u v) → γ = 1)).1 h
  refine ⟨Subtype.val '' interior A, hO.isOpenMap_subtype_val _ isOpen_interior,
    ⟨_, mem_interior_iff_mem_nhds.2 hA, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ ⟨γ, hγ, he⟩
    have hl := hΓ γ hγ
    have hf : ∀ u v, (F.R y.1).form (γ u) (γ v) = (F.R x.1).form u v := fun u v => by
      rw [F.form_eq, F.form_eq]
      rcases hF with e | e
      · rw [e]
        exact hl.1 u v
      · rw [e]
        exact congrArg Neg.neg (hl.1 u v)
    obtain rfl := hA' x (interior_subset hx) y (interior_subset hy) γ hl.congr (reForm_eqv hf he)
    exact (F.univ (F.R y.1) (F.form_eq _) (F.sig _ y.2)).unique ⟨x.2, he⟩ ⟨y.2, LinearEquiv.refl _ _, fun _ => rfl⟩

end SheetDecomposition
end
end

