import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0003
import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0005
import Development.WeilBound.CoreStatements.SesquilinearFractions.FrameBCLin
import Development.WeilBound.CoreStatements.SesquilinearFractions.SpMapMonoOfFraction
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0034
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0120

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.GFrameBC
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf.EigenspaceComposition

theorem epi_spMap {K L : Type} [Field K] [Field L] (a : K →+* L) : Epi (spMap a) := by
  constructor
  intro X g₁ g₂ h
  obtain ⟨⟨x₁, φ₁⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective g₁
  obtain ⟨⟨x₂, φ₂⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective g₂
  have h' : (Scheme.SpecToEquivOfField L X).symm ⟨x₁, φ₁ ≫ CommRingCat.ofHom a⟩ =
      (Scheme.SpecToEquivOfField L X).symm ⟨x₂, φ₂ ≫ CommRingCat.ofHom a⟩ := by
    simpa [Scheme.SpecToEquivOfField, spMap, Spec.map_comp, Category.assoc] using h
  have h'' := (Scheme.SpecToEquivOfField L X).symm.injective h'
  rw [Scheme.SpecToEquivOfField_eq_iff] at h''
  obtain ⟨e, he⟩ := h''
  dsimp only at e he
  subst e
  have hφ : φ₁ = φ₂ := by
    ext z
    have hz := congrArg (fun m => m.hom z) he
    simp at hz
    exact a.injective hz
  rw [hφ]

theorem one_left' {S : Scheme.{0}} (G : Over S) [GrpObj G] (Y : Over S) :
    (1 : Y ⟶ G).left = Y.hom ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

end PositivityTheory.Xgf.EigenspaceComposition

namespace PositivityTheory.Xgf

private theorem isTanAt_base_change_iff {S : Scheme.{0}} (G : Over S) [GrpObj G] {F F' : Type} [Field F] [Field F']
    (f : F →+* F') (x : Sp F ⟶ S) (x' : Sp F' ⟶ S) (hx : x' = spMap f ≫ x)
    (w : epsAt x ⟶ G) (w' : epsAt x' ⟶ G) (hw : w'.left = spMap (dualMap f) ≫ w.left) :
    IsTanAt G x' w' ↔ IsTanAt G x w := by
  have key : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom F' F' F').toRingHom) ≫ spMap (dualMap f) =
      spMap f ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom F F F).toRingHom) := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro a
    simp [dualMap]
  haveI := EigenspaceComposition.epi_spMap f
  show _ = (1 : Over.mk x' ⟶ G).left ↔ _ = (1 : Over.mk x ⟶ G).left
  rw [EigenspaceComposition.one_left', EigenspaceComposition.one_left', hw, ← Category.assoc, key, Category.assoc]
  simp only [Over.mk_hom, hx, Category.assoc]
  constructor
  · intro h
    exact (cancel_epi (spMap f)).mp h
  · intro h
    rw [h]

open PositivityTheory.Xgf.EigenspaceComposition in
theorem tangent_vectors_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (F F' : Type) [Field F] [Field F'] (f : F →+* F') (x : Sp F ⟶ S) (x' : Sp F' ⟶ S) (τ : 𝓞 E →+* F) (n : ℕ) (v : Fin n → (epsAt x ⟶ t.G)), x' = spMap f ≫ x → (∃ v' : Fin n → (epsAt x' ⟶ t.G), ∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) ∧ ∀ v' : Fin n → (epsAt x' ⟶ t.G), (∀ k, (v' k).left = spMap (dualMap f) ≫ (v k).left) → (IsEigFrame t.act x τ v ↔ IsEigFrame t.act x' (f.comp τ) v') := by
  intro E _ _ _ H S t F F' _ _ f x x' τ n v hx'
  have hcomp : ∀ w : epsAt x ⟶ t.G, ∃ w' : epsAt x' ⟶ t.G, w'.left = spMap (dualMap f) ≫ w.left := by
    intro w
    refine ⟨Over.homMk (spMap (dualMap f) ≫ w.left) ?_, rfl⟩
    rw [Category.assoc, Over.w w]
    simp only [epsAt, Over.mk_hom, hx', spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    apply RingHom.ext
    intro a
    simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨⟨fun k => Classical.choose (hcomp (v k)), fun k => Classical.choose_spec (hcomp (v k))⟩, ?_⟩
  intro v' hv'
  have htan : ∀ k, IsTanAt t.G x' (v' k) ↔ IsTanAt t.G x (v k) :=
    fun k => isTanAt_base_change_iff t.G f x x' hx' (v k) (v' k) (hv' k)
  by_cases hT : ∀ k, IsTanAt t.G x (v k)
  · obtain ⟨N, M, ρ, hρ, hbc⟩ := lie_model_action_base_change E H S t F x
    obtain ⟨M', ρ', hρ', hpt, hc⟩ := hbc F' f x' hx'
    choose u hu using fun k => M.onto (v k) (hT k)
    have hv'eq : v' = fun k => M'.pt (f ∘ u k) := by
      funext k
      apply Over.OverMorphism.ext
      rw [hv' k, hpt, hu k]
    have hveq : v = fun k => M.pt (u k) := funext fun k => (hu k).symm
    rw [hv'eq, hveq, ((lie_model_eigenvectors_action S F t.G x _ M).2 _ t.act ρ τ hρ).2 n u,
      ((lie_model_eigenvectors_action S F' t.G x' _ M').2 _ t.act ρ' (f.comp τ) hρ').2 n (fun k => f ∘ u k)]
    exact EigenspaceComposition.core (τ := τ) hc u
  · push_neg at hT
    obtain ⟨k, hk⟩ := hT
    constructor
    · intro h
      exact absurd (h.1 k).1 hk
    · intro h
      exact absurd ((htan k).1 (h.1 k).1) hk

end PositivityTheory.Xgf
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.GIntFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf

private theorem isTanAt_iff_epsScale_zero_comp_eq_one {R : Type} [CommRing R] {S : Scheme} (x : Sp R ⟶ S) (G : Over S) [GrpObj G]
    (v : epsAt x ⟶ G) : IsTanAt G x v ↔ LieTangent.epsScale x 0 ≫ v = 1 := by
  have one_left : ∀ (Y : Over S), (1 : Y ⟶ G).left = Y.hom ≫ (η[G] : 𝟙_ (Over S) ⟶ G).left := by
    intro Y
    rw [Hom.one_def, Over.comp_left]
    congr 1
  have hmul : Spec.map (CommRingCat.ofHom (CompanionTheory.Ar.epsMul (0 : R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply RingHom.ext
    intro a
    ext <;> simp [CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  have hid : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    apply RingHom.ext
    intro a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hsec : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hid, CommRingCat.ofHom_id, Spec.map_id]
  unfold IsTanAt
  constructor
  · intro h
    apply Over.OverMorphism.ext
    rw [Over.comp_left, one_left]
    change Spec.map (CommRingCat.ofHom (CompanionTheory.Ar.epsMul (0 : R))) ≫ v.left = _
    rw [hmul, Category.assoc, h, one_left]
    simp [epsAt]
  · intro h
    rw [one_left]
    have h2 := congrArg Over.Hom.left h
    rw [Over.comp_left, one_left] at h2
    change Spec.map (CommRingCat.ofHom (CompanionTheory.Ar.epsMul (0 : R))) ≫ v.left = _ at h2
    rw [hmul, Category.assoc] at h2
    have h3 := congrArg (fun q => Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ q) h2
    simp only [epsAt, Over.mk_hom, ← Category.assoc, hsec, Category.id_comp] at h3
    rw [h3]
    simp

open BaseChangeTangents in
theorem lie_model_extends_over_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (K : Type) [Field K] (V : Subring K) [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V K] (y : Sp K ⟶ Xo.XF c) (T : SAB H (Sp V)) (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y)) (m' : SABMap tK T (spMap (algebraMap V K))) (U : Type) [AddCommGroup U] [Module K U] (M : LieModel Xo.univ.t.G (under y) U) (ρ : 𝓞 E →+* Module.End K U) (σ : E →+* K) (I : Type) [Fintype I] (n r : ℕ) (e : Fin n ≃ I) (uV : Fin n → (epsAt (𝟙 (Sp V)) ⟶ T.G)) (u : I → U) (v : Fin r → U), M.IsActOf Xo.univ.t.act.act ρ → (∀ a : 𝓞 E, σ (a : E) ∈ V) → (∀ k, IsTanAt T.G _ (uV k)) → (∀ w, IsTanAt T.G _ w → ∃! cc : Fin n → V, IsComb cc uV w) → (∀ k, ∃ s : Sp (DualNumber K) ⟶ tK.G.left, s ≫ m.φ = (M.pt (u (e k))).left ∧ s ≫ m'.φ = spMap (dualMap (algebraMap V K)) ≫ (uV k).left) → LinearIndependent K v → Submodule.span V (Set.range u) ⊓ (HT.eigSp ρ σ).restrictScalars V = Submodule.span V (Set.range v) → LinearIndependent K u ∧ IsIntFrame m m' (σ.comp (algebraMap (𝓞 E) E)) (fun a => M.pt (v a)) := by
  intro E _ _ _ H D l Xo c K _ V _ _ _ y T tK m m' U _ _ M ρ σ I _ n r e uV u v hρ hσ huVt huVb hcorr hv hspan
  have hinj : Function.Injective (algebraMap V K) := IsFractionRing.injective V K
  let P : (epsAt (𝟙 (Sp V)) ⟶ T.G) → (epsAt (under y) ⟶ Xo.univ.t.G) :=
    fun w => BaseChangeTangents.push m.cart (BaseChangeTangents.bcTan (algebraMap V K) m'.cart w)
  have hP1 : P 1 = 1 := by
    simp only [P, BaseChangeTangents.bcTan_one]
    exact map_one (BaseChangeTangents.pushHom m.cart)
  have hPscale : ∀ (a : V) w, P (LieTangent.epsScale (𝟙 (Sp V)) a ≫ w) =
      LieTangent.epsScale (under y) (algebraMap V K a) ≫ P w := by
    intro a w
    simp only [P, BaseChangeTangents.bcTan_scale, BaseChangeTangents.push_scale]
  have hPcomb : ∀ {N : ℕ} (cc : Fin N → V) (w : Fin N → (epsAt (𝟙 (Sp V)) ⟶ T.G)),
      P (List.ofFn fun i => LieTangent.epsScale (𝟙 (Sp V)) (cc i) ≫ w i).prod =
        (List.ofFn fun i => LieTangent.epsScale (under y) (algebraMap V K (cc i)) ≫ P (w i)).prod := by
    intro N cc w
    simp only [P, BaseChangeTangents.bcTan_comb, BaseChangeTangents.push_comb]
  have hPact : ∀ (a : 𝓞 E) w, P (w ≫ T.act.act a) = P w ≫ Xo.univ.t.act.act a := by
    intro a w
    simp only [P]
    rw [BaseChangeTangents.bcTan_act _ m'.cart (tK.act.act a) (T.act.act a) (m'.act a),
      BaseChangeTangents.push_act m.cart (tK.act.act a) (Xo.univ.t.act.act a) (m.act a)]
  have tprod : ∀ (L : List (epsAt (𝟙 (Sp V)) ⟶ T.G)), (∀ w ∈ L, IsTanAt T.G (𝟙 (Sp V)) w) →
      IsTanAt T.G (𝟙 (Sp V)) L.prod := by
    intro L
    induction L with
    | nil =>
      intro _
      simpa using LieTangent.isTanAt_one
    | cons a L ih =>
      intro h
      rw [List.prod_cons]
      exact LieTangent.isTanAt_mul (h a (by simp)) (ih fun w hw => h w (by simp [hw]))
  have tcomb : ∀ {N : ℕ} (cc : Fin N → V) (w : Fin N → (epsAt (𝟙 (Sp V)) ⟶ T.G)),
      (∀ k, IsTanAt T.G (𝟙 (Sp V)) (w k)) →
        IsTanAt T.G (𝟙 (Sp V)) (List.ofFn fun i => LieTangent.epsScale (𝟙 (Sp V)) (cc i) ≫ w i).prod := by
    intro N cc w hw
    apply tprod
    intro z hz
    simp only [List.mem_ofFn] at hz
    obtain ⟨i, rfl⟩ := hz
    exact LieTangent.isTanAt_scale _ (hw i)
  have hPinj : ∀ w w', IsTanAt T.G (𝟙 (Sp V)) w → IsTanAt T.G (𝟙 (Sp V)) w' → P w = P w' → w = w' := by
    intro w w' hw hw' h
    exact BaseChangeTangents.bcTan_inj _ m'.cart hinj hw hw' (BaseChangeTangents.push_inj m.cart h)
  have hM0 : M.pt 0 = 1 := by
    have h := M.add 0 0
    rw [add_zero] at h
    exact mul_eq_left.mp h.symm
  have hMscale : ∀ (a : K) (z : U), M.pt (a • z) = LieTangent.epsScale (under y) a ≫ M.pt z := by
    intro a z
    apply Over.OverMorphism.ext
    rw [M.smul, Over.comp_left]
    rfl
  have hPu : ∀ k, P (uV k) = M.pt (u (e k)) := by
    intro k
    obtain ⟨s, hs1, hs2⟩ := hcorr k
    have hs := BaseChangeTangents.eq_bcTan_left (algebraMap V K) m'.cart rfl (uV k) s hs2
    apply Over.OverMorphism.ext
    simp only [P]
    rw [BaseChangeTangents.push_left, ← hs]
    exact hs1
  have hPsum : ∀ {N : ℕ} (cc : Fin N → V) (w : Fin N → (epsAt (𝟙 (Sp V)) ⟶ T.G)) (z : Fin N → U),
      (∀ k, P (w k) = M.pt (z k)) →
        P (List.ofFn fun i => LieTangent.epsScale (𝟙 (Sp V)) (cc i) ≫ w i).prod =
          M.pt (∑ i, algebraMap V K (cc i) • z i) := by
    intro N cc w z hwz
    rw [hPcomb]
    simp only [hwz]
    exact BaseChangeTangents.prod_pt M _ z
  have hsmul : ∀ (a : V) (z : U), a • z = algebraMap V K a • z := fun a z => (algebraMap_smul K a z).symm
  have hliV : LinearIndependent V u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    let cc : Fin n → V := fun k => g (e k)
    have hsum : ∑ k, algebraMap V K (cc k) • u (e k) = 0 := by
      calc ∑ k, algebraMap V K (cc k) • u (e k) = ∑ k, g (e k) • u (e k) :=
            Finset.sum_congr rfl fun k _ => (hsmul _ _).symm
        _ = ∑ i, g i • u i := Equiv.sum_comp e (fun i => g i • u i)
        _ = 0 := hg
    have hcomb1 : P (List.ofFn fun k => LieTangent.epsScale (𝟙 (Sp V)) (cc k) ≫ uV k).prod = P 1 := by
      rw [hPsum cc uV (fun k => u (e k)) hPu]
      simp only [hsum, hM0, hP1]
    have heq1 := hPinj _ _ (tcomb cc uV huVt) LieTangent.isTanAt_one hcomb1
    obtain ⟨c0, _, huniq⟩ := huVb 1 LieTangent.isTanAt_one
    have hc1 : IsComb cc uV 1 := by
      rw [BaseChangeTangents.isComb_iff]
      exact heq1.symm
    have hc0 : IsComb (fun _ => (0 : V)) uV 1 := by
      rw [BaseChangeTangents.isComb_iff]
      have h0 : ∀ k, LieTangent.epsScale (𝟙 (Sp V)) (0 : V) ≫ uV k = 1 :=
        fun k => (isTanAt_iff_epsScale_zero_comp_eq_one _ _ _).mp (huVt k)
      simp only [h0, List.ofFn_const, List.prod_replicate, one_pow]
    have hcc := (huniq cc hc1).trans (huniq _ hc0).symm
    have hk := congrFun hcc (e.symm i)
    simpa [cc] using hk
  have hliK : LinearIndependent K u := LinearIndependent.localization K (nonZeroDivisors V) hliV
  refine ⟨hliK, ?_⟩
  let σV : 𝓞 E →+* V := (σ.comp (algebraMap (𝓞 E) E)).codRestrict V (fun a => hσ a)
  have hσV : ∀ a, algebraMap V K (σV a) = σ (a : E) := fun a => rfl
  have hvmem : ∀ a, v a ∈ Submodule.span V (Set.range u) ⊓ (HT.eigSp ρ σ).restrictScalars V := by
    intro a
    rw [hspan]
    exact Submodule.subset_span ⟨a, rfl⟩
  choose d hd using fun a => (Submodule.mem_span_range_iff_exists_fun V).mp (hvmem a).1
  let vV : Fin r → (epsAt (𝟙 (Sp V)) ⟶ T.G) :=
    fun a => (List.ofFn fun k => LieTangent.epsScale (𝟙 (Sp V)) (d a (e k)) ≫ uV k).prod
  have hPv : ∀ a, P (vV a) = M.pt (v a) := by
    intro a
    rw [hPsum (fun k => d a (e k)) uV (fun k => u (e k)) hPu, ← hd a]
    congr 1
    rw [← Equiv.sum_comp e (fun i => d a i • u i)]
    exact Finset.sum_congr rfl fun k _ => (hsmul _ _).symm
  have hvVt : ∀ a, IsTanAt T.G (𝟙 (Sp V)) (vV a) := fun a => tcomb _ uV huVt
  have heig : ∀ w (z : U), IsTanAt T.G (𝟙 (Sp V)) w → P w = M.pt z →
      (IsEigVec T.act (𝟙 (Sp V)) σV w ↔ z ∈ HT.eigSp ρ σ) := by
    intro w z hw hwz
    have key : ∀ a : 𝓞 E, (Over.Hom.left (w ≫ T.act.act a) = spMap (CompanionTheory.Ar.epsMul (σV a)) ≫ Over.Hom.left w) ↔
        ρ a z = σ (a : E) • z := by
      intro a
      have e1 : (Over.Hom.left (w ≫ T.act.act a) = spMap (CompanionTheory.Ar.epsMul (σV a)) ≫ Over.Hom.left w) ↔
          w ≫ T.act.act a = LieTangent.epsScale (𝟙 (Sp V)) (σV a) ≫ w := by
        constructor
        · intro h
          apply Over.OverMorphism.ext
          rw [h, Over.comp_left]
          rfl
        · intro h
          rw [h, Over.comp_left]
          rfl
      rw [e1]
      haveI := T.act.hom a
      constructor
      · intro h
        have h2 := congrArg P h
        rw [hPact, hPscale, hwz, hσV] at h2
        apply M.inj
        rw [hMscale, ← h2]
        exact hρ a z
      · intro h
        apply hPinj _ _ (TransportLieModel.isTanAt_comp hw _) (LieTangent.isTanAt_scale _ hw)
        rw [hPact, hPscale, hwz, hσV, ← hMscale, ← h]
        exact (hρ a z).symm
    simp only [IsEigVec, hw, true_and, key]
    simp only [HT.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero]
  refine ⟨σV, vV, ?_, ?_, ?_⟩
  · exact RingHom.ext fun a => rfl
  · refine ⟨?_, ?_⟩
    · intro a
      exact (heig (vV a) (v a) (hvVt a) (hPv a)).mpr ((Submodule.restrictScalars_mem _ _ _).mp (hvmem a).2)
    · intro w hw
      have hwt : IsTanAt T.G (𝟙 (Sp V)) w := hw.1
      obtain ⟨cc, hcc, _⟩ := huVb w hwt
      rw [BaseChangeTangents.isComb_iff] at hcc
      have hPw : P w = M.pt (∑ k, algebraMap V K (cc k) • u (e k)) := by
        rw [hcc]
        exact hPsum cc uV (fun k => u (e k)) hPu
      have hzE := (heig w _ hwt hPw).mp hw
      have hzU : (∑ k, algebraMap V K (cc k) • u (e k)) ∈ Submodule.span V (Set.range u) := by
        apply Submodule.sum_mem
        intro k _
        rw [← hsmul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨e k, rfl⟩)
      have hzv : (∑ k, algebraMap V K (cc k) • u (e k)) ∈ Submodule.span V (Set.range v) := by
        rw [← hspan]
        exact ⟨hzU, hzE⟩
      obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun V).mp hzv
      have hPg : P (List.ofFn fun a => LieTangent.epsScale (𝟙 (Sp V)) (g a) ≫ vV a).prod =
          M.pt (∑ k, algebraMap V K (cc k) • u (e k)) := by
        rw [hPsum g vV v hPv, ← hg]
        exact congrArg M.pt (Finset.sum_congr rfl fun a _ => (hsmul _ _).symm)
      refine ⟨g, ?_, ?_⟩
      · show Fl.IsComb g vV w
        rw [BaseChangeTangents.isComb_iff]
        exact hPinj _ _ hwt (tcomb g vV hvVt) (hPw.trans hPg.symm)
      · intro g' hg'
        change Fl.IsComb g' vV w at hg'
        rw [BaseChangeTangents.isComb_iff] at hg'
        have h1 : M.pt (∑ a, algebraMap V K (g' a) • v a) = M.pt (∑ a, algebraMap V K (g a) • v a) := by
          rw [← hPsum g' vV v hPv, ← hg', hPw, ← hg]
          exact congrArg M.pt (Finset.sum_congr rfl fun a _ => hsmul _ _)
        have h2 := M.inj h1
        funext a
        apply hinj
        have h3 := Fintype.linearIndependent_iff.mp hv (fun a => algebraMap V K (g' a) - algebraMap V K (g a))
          (by simp only [sub_smul, Finset.sum_sub_distrib, h2, sub_self]) a
        exact sub_eq_zero.mp h3
  · intro a
    refine ⟨(BaseChangeTangents.bcTan (algebraMap V K) m'.cart (vV a)).left, ?_, BaseChangeTangents.bcTan_left _ _ _⟩
    exact (BaseChangeTangents.push_left m.cart _).symm.trans (congrArg Over.Hom.left (hPv a))

end PositivityTheory.Xgf
end
end

-- bundled from Development.WeilBound.CoreStatements.SesquilinearFractions.GLieInt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.isogeny_decomposition_product

theorem tan_comp {S : Scheme.{0}} {R : Type} [CommRing R] {A B : Over S} [GrpObj A] [GrpObj B] {x : Sp R ⟶ S}
    (t : epsAt x ⟶ A) (ht : IsTanAt A x t) (g : A ⟶ B) [IsMonHom g] : IsTanAt B x (t ≫ g) := by
  unfold IsTanAt at ht ⊢
  rw [Over.comp_left, ← Category.assoc, ht, ← Over.comp_left, MonObj.one_comp]

theorem one_left {S : Scheme.{0}} {X A : Over S} [GrpObj A] : (1 : X ⟶ A).left = X.hom ≫ η[A].left := by
  rw [Hom.one_def]; simp

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  simp [spMap, ← Spec.map_comp]

theorem bc_one {R V : Type} [CommRing R] [CommRing V] (f : R →+* V) {A : Over (Sp R)} [GrpObj A] :
    spMap (dualMap f) ≫ (1 : epsR R ⟶ A).left = (1 : epsAt (spMap f ≫ 𝟙 (Sp R)) ⟶ A).left := by
  rw [one_left, one_left, ← Category.assoc]
  congr 1
  simp only [Over.mk_hom, Category.comp_id]
  rw [spMap_comp, spMap_comp]
  congr 1
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem bc_eps {R V : Type} [CommRing R] [CommRing V] (f : R →+* V) (N : ℕ) :
    spMap (dualMap f) ≫ spMap (GlobalTheory.CompanionTheory.Ar.epsMul (N : R)) = spMap (GlobalTheory.CompanionTheory.Ar.epsMul (N : V)) ≫ spMap (dualMap f) := by
  rw [spMap_comp, spMap_comp]
  congr 1
  ext a <;> simp [dualMap, GlobalTheory.CompanionTheory.Ar.epsMul, TrivSqZeroExt.algebraMap_eq_inl, mul_comm]

theorem pow_left {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] (v : epsR R ⟶ A)
    (hv : IsLieBasis ![v]) (N : ℕ) :
    v.left ≫ (𝟙 A ^ N).left = spMap (GlobalTheory.CompanionTheory.Ar.epsMul (N : R)) ≫ v.left := by
  obtain ⟨E, _, _, ⟨M⟩⟩ := lieModel_exists (Sp R) A R (𝟙 (Sp R))
  obtain ⟨b, hb⟩ := basis_of_lieBasis v hv M
  have e1 : toAt v = M.pt (b 0) := Over.OverMorphism.ext (by rw [toAt_left, hb])
  have h := congrArg Over.Hom.left (comp_pow' (toAt v) (𝟙 A) N)
  rw [Category.comp_id, e1, ← pt_nsmul, Over.comp_left, ← e1, toAt_left, ← Nat.cast_smul_eq_nsmul R,
    M.smul, ← e1, toAt_left] at h
  exact h

end PositivityTheory.Xgf.isogeny_decomposition_product

namespace PositivityTheory.Xgf

open PositivityTheory.Xgf.isogeny_decomposition_product in
theorem isogeny_decomposition_product : ∀ (R V : Type) [CommRing R] [CommRing V] [IsLocalRing V] (f : R →+* V) (n N : ℕ) (C : Fin n → Out.PolAV (Sp R)) (v : ∀ k, epsR R ⟶ (C k).A) (B : Out.PolAV (Sp R)) (ψ : ∀ k, (C k).A ⟶ B.A) (χ : ∀ k, B.A ⟶ (C k).A) (G : Over (Sp V)) [GrpObj G] (π : G.left ⟶ B.A.left), B.g = n → (∀ k, IsLieBasis ![v k]) → (∀ k, IsMonHom (ψ k)) → (∀ k, IsMonHom (χ k)) → (∀ k, ψ k ≫ χ k = 𝟙 (C k).A ^ N) → (∀ k k', k ≠ k' → ψ k ≫ χ k' = 1) → IsUnit (N : V) → IsGrpPullback G B.A (spMap f) π → ∃ u : Fin n → (epsAt (𝟙 (Sp V)) ⟶ G), (∀ k, (u k).left ≫ π = spMap (dualMap f) ≫ (v k).left ≫ (ψ k).left) ∧ (∀ k, IsTanAt G _ (u k)) ∧ ∀ w, IsTanAt G _ w → ∃! cc : Fin n → V, IsComb cc u w := by
  intro R V _ _ _ f n N C v B ψ χ G _ π hg hv hψ hχ hpc hpo hN hpb
  obtain ⟨EBR, _, _, ⟨MBR⟩⟩ := lieModel_exists (Sp R) B.A R (𝟙 (Sp R))
  obtain ⟨EBV, _, _, ⟨MBV⟩⟩ := lieModel_exists (Sp R) B.A V (spMap f ≫ 𝟙 (Sp R))
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear (Sp R) B.A R V f (𝟙 _) EBR EBV MBR MBV
  have hx : spMap f ≫ 𝟙 (Sp R) = 𝟙 (Sp V) ≫ spMap f := by simp
  obtain ⟨MG, hMG⟩ := (GlobalTheory.T.lie_model_pullback_equivalence (Sp R) (Sp V) B.A G (spMap f) π hpb V (𝟙 (Sp V)) EBV).1 (castM hx MBV)
  have hMG' : ∀ e, (MG.pt e).left ≫ π = (MBV.pt e).left := fun e => (hMG e).trans (castM_left hx MBV e)

  have hvt : ∀ k, IsTanAt B.A (𝟙 (Sp R)) (toAt (v k) ≫ ψ k) := fun k => by
    haveI := hψ k; exact tan_comp _ (toAt_tan (v k) ((hv k).1 0)) (ψ k)
  choose eR heR using fun k => MBR.onto _ (hvt k)
  let EV : Fin n → EBV := fun k => j (eR k)
  have hlift : ∀ e, (MBV.pt (j e)).left = spMap (dualMap f) ≫ (MBR.pt e).left := fun e =>
    (Category.comp_id (MBV.pt (j e)).left).symm.trans (hj e)
  have hEV : ∀ k, (MBV.pt (EV k)).left = spMap (dualMap f) ≫ (v k).left ≫ (ψ k).left := fun k => by
    show (MBV.pt (j (eR k))).left = _
    rw [hlift, heR, Over.comp_left, toAt_left]

  choose EC iC mC MC bC hbC using fun k => lc (C k) (v k) (hv k) V f
  have hd : ∀ k, ∃ A : EBV →ₗ[V] EC k, ∀ e, (MC k).pt (A e) = MBV.pt e ≫ χ k := fun k => by
    haveI := hχ k
    exact (GlobalTheory.T.lie_model_functorial_map (Sp R) B.A (C k).A V (spMap f ≫ 𝟙 (Sp R)) EBV (EC k) MBV (MC k) (χ k)).exists
  choose dχ hdχ using hd
  let fV : Fin n → (EBV →ₗ[V] V) := fun k => ((bC k).coord 0).comp (dχ k)
  have hval : ∀ i k, fV k (EV i) = if i = k then (N : V) else 0 := by
    intro i k
    have hleft : ((MC k).pt (dχ k (EV i))).left = spMap (dualMap f) ≫ (v i).left ≫ (ψ i ≫ χ k).left := by
      rw [hdχ, Over.comp_left, hEV, Over.comp_left]; simp only [Category.assoc]
    split_ifs with hik
    · subst hik
      have e2 : dχ i (EV i) = (N : V) • bC i 0 := by
        apply (MC i).inj
        apply Over.OverMorphism.ext
        rw [hleft, hpc, (MC i).smul, hbC, pow_left (v i) (hv i) N, ← Category.assoc, bc_eps, Category.assoc]
      simp [fV, e2]
    · have e2 : dχ k (EV i) = 0 := by
        apply (MC k).inj
        apply Over.OverMorphism.ext
        rw [hleft, hpo i k hik, pt_zero, ← bc_one f]
        congr 1
        rw [← Over.comp_left, MonObj.comp_one]
      simp [fV, e2]
  obtain ⟨bB⟩ := GlobalTheory.T.lie_model_free_of_smooth (Sp R) B.A n (hg ▸ B.smoothDim) V (spMap f ≫ 𝟙 (Sp R)) EBV MBV
  obtain ⟨hli, hsp⟩ := GlobalTheory.T.dual_family_is_basis V EBV n bB EV fV (N : V) hN hval
  have bridge := (GlobalTheory.T.lie_model_eigenvectors_action (Sp V) V G (𝟙 (Sp V)) EBV MG).1 n
  refine ⟨fun k => MG.pt (EV k), fun k => hMG' (EV k) ▸ hEV k, fun k => MG.tan _, fun w hw => ?_⟩
  obtain ⟨e, rfl⟩ := MG.onto w hw
  have hmem : e ∈ Submodule.span V (Set.range EV) := hsp ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 hmem
  refine ⟨c, (bridge c EV _).2 (by rw [hc]), fun c' hc' => ?_⟩
  have h1 := MG.inj ((bridge c' EV _).1 hc')
  rw [← hc] at h1
  have h2 := Fintype.linearIndependent_iff.1 hli (c' - c) (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h1, sub_self])
  funext i
  have := h2 i
  rw [Pi.sub_apply, sub_eq_zero] at this
  exact this

end PositivityTheory.Xgf

end
end

