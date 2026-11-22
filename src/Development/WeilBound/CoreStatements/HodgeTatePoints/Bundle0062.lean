import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoFrame
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels GlobalTheory.KeyUnitModels GlobalTheory.KeyCancel IsLocalRing

namespace PositivityTheory.HtPt.Kftwo

theorem isFibreOf_trans {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {G : Over (Sp R)} [GrpObj G]
    [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec G))} {θ : L.Sec} {n : ℕ}
    {v : Fin n → (epsR R ⟶ G)} {x' : KeyIn R'} {x'' : KeyIn R''} {f : R →+* R'} {f' : R' →+* R''}
    (H : IsFibreOf x' G L rig θ v f) (H' : KeyPB x'' x' f') : IsFibreOf x'' G L rig θ v (f'.comp f) := by
  obtain ⟨φ, he, w, hg, F, hp, hw, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := H'
  have g := (isGen_iff w).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp x'.P.isLB w w' g g' hL x''.P.isLB
  have he'' : eSec x''.P.A ≫ φ' ≫ φ = spMap (f'.comp f) ≫ eSec G := by
    rw [← Category.assoc, he', Category.assoc, he, spMap_comp, Category.assoc]
  refine ⟨φ' ≫ φ, he'', w'', hg'.trans hg, F'.comp F, (hp'.comp hp).congr (spMap_comp f f').symm rfl,
    (isGen_iff w'').2 (T.pgen_comp x'.P.isLB g g'), ?_, ?_, fun a => ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec G) _ x'.rig rig (spMap f) _
      (rigPull_le φ (spMap f) he L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec x'.P.A) _ x''.rig x'.rig (spMap f') _
      (rigPull_le φ' (spMap f') he' x'.P.L) (fun _ => rfl)).1 hr'
    have r₂ := T.pmaps_comp x'.P.isLB (fun _ => he') r₀ r₁
    rw [← spMap_comp] at r₂
    exact (maps_iff w'' _ (fun _ => eSec G) _ x''.rig rig (spMap (f'.comp f)) _
      (rigPull_le (φ' ≫ φ) (spMap (f'.comp f)) he'' L) (fun _ => rfl)).2 r₂
  · refine (appLE_eq_iff_stalk w'' θ x''.th).2 fun Z q z j k hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart x'.P.isLB (φ' (q z))
    have a := (appLE_eq_iff_stalk w θ x'.th).1 hs Z (q ≫ φ') z j i hj hi
    have b := (appLE_eq_iff_stalk w' x'.th x''.th).1 hs' Z q z i k hi hk
    rw [T _ q z j i k hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [RingHom.comp_apply, hF, hF', RingHom.comp_apply]
  · rw [RingHom.comp_apply, hε, hε']
  · rw [← Category.assoc, hv', Category.assoc, hv, spMap_comp, Category.assoc]
    rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_isFibreOf_pull {R R' R'' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] [CommRing R'']
    {f : R →+* R'} [IsLocalHom f] {f' : R' →+* R''} {t : SAB H (Sp R)} {t' : SAB H (Sp R')} (m : SABMap t' t (spMap f))
    {θ : t.PP.L.Sec} {n : ℕ} {v : Fin n → (epsR R ⟶ t.G)} (hθ : NonzeroClosed (X := t.G) θ) (hv : IsLieBasis v)
    {x : KeyIn R''} (hx : IsFibreOf x t.G t.PP.L t.PP.rig θ v (f'.comp f)) :
    ∃ (θ' : t'.PP.L.Sec) (v' : Fin n → (epsR R' ⟶ t'.G)), NonzeroClosed (X := t'.G) θ' ∧ IsLieBasis v' ∧
      IsFibreOf x t'.G t'.PP.L t'.PP.rig θ' v' f' := by
  obtain ⟨φ'', he'', w'', hg'', F'', hc'', hw'', hr'', hs'', hF'', hFe'', hv''⟩ := hx
  obtain ⟨w, hw, hr, -⟩ := m.lin
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨θ', hs⟩ := sec_pull_down g t.PP.isLB t'.PP.isLB θ
  obtain ⟨v', hv', hvv⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ f t.G t'.G m.φ m.cart t.semi.smooth n v hv
  have he : eSec t'.G ≫ m.φ = spMap f ≫ eSec t.G := m.cm.e_comm.trans (congrArg (· ≫ eSec t.G) m.base)
  have hrig : m.cm.rigPull t.PP.L t.PP.rig = rigPullOf m.φ (spMap f) he t.PP.L t.PP.rig := by
    have key : ∀ (a b : Sp R' ⟶ Sp R) (_ : a = b) ha hb,
        rigPullOf (G' := t'.G) m.φ a ha t.PP.L t.PP.rig = rigPullOf m.φ b hb t.PP.L t.PP.rig := by
      rintro a b rfl _ _
      rfl
    exact key _ _ m.base _ _
  rw [hrig] at hr
  refine ⟨θ', v', ?_, hv', ?_⟩
  · obtain ⟨z, hz, hz'⟩ := hθ
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback m.cart.1 z (closedPoint R')
      (hz.trans (IsLocalRing.comap_closedPoint f).symm)
    obtain ⟨k, hb⟩ := TopologicalSpace.Opens.mem_iSup.1 hz'
    have hk : m.φ y ∈ t.PP.L.U k := t.G.left.basicOpen_le _ hb
    obtain ⟨l, hl⟩ := exists_chart t'.PP.isLB y
    have u : IsUnit (gs (𝟙 _) (m.φ y) _ (θ.f k)) := by
      rw [gs_eq (𝟙 _) (m.φ y) _ hk]; exact (t.G.left.mem_basicOpen _ _ hk).1 hb
    have u₁ : IsUnit (gs m.φ y _ (θ.f k)) := by rw [gs_stalkMap m.φ y _ hk]; exact u.map _
    have e := hs _ (𝟙 _) y k l hk hl
    rw [Category.id_comp] at e
    have u₂ := isUnit_of_mul_isUnit_right (e ▸ u₁)
    rw [gs_eq (𝟙 _) y _ hl] at u₂
    exact ⟨y, hy, TopologicalSpace.Opens.mem_iSup.2 ⟨l, (t'.G.left.mem_basicOpen _ _ hl).2 u₂⟩⟩
  have hsp : spMap (f'.comp f) = spMap f' ≫ spMap f := spMap_comp _ _
  have hc := m.cart
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : x.P.A.left ⟶ t'.G.left, φ' ≫ m.φ = φ'' ∧ φ' ≫ t'.G.hom = x.P.A.hom ≫ spMap f' :=
    ⟨hp.lift φ'' (x.P.A.hom ≫ spMap f') (by rw [hc''.1.w, Category.assoc, hsp]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have he' : eSec x.P.A ≫ φ' = spMap f' ≫ eSec t'.G := by
    apply hp.hom_ext
    · rw [Category.assoc, he'', hsp, Category.assoc, Category.assoc, he]
    · have a₁ : eSec x.P.A ≫ x.P.A.hom = 𝟙 _ := Over.w η[x.P.A]
      have a₂ : eSec t'.G ≫ t'.G.hom = 𝟙 _ := Over.w η[t'.G]
      rw [Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  obtain ⟨w', T⟩ := exists_cancel t.PP.isLB w w'' g g'' t'.PP.isLB x.P.isLB
  have r := (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig (spMap f) _ (rigPull_le m.φ (spMap f) he t.PP.L)
    (fun _ => rfl)).1 hr
  have r'' := (maps_iff w'' _ (fun _ => eSec t.G) _ x.rig t.PP.rig (spMap (f'.comp f)) _
    (rigPull_le (φ' ≫ m.φ) (spMap (f'.comp f)) he'' t.PP.L) (fun _ => rfl)).1 hr''
  rw [hsp] at r''
  have hFF : (Chart.dualMapR f').comp (Chart.dualMapR f) = F'' := dualNumber_ringHom_ext
    (fun a => by
      rw [RingHom.comp_apply, hF'']
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [RingHom.comp_apply, hFe'']
      ext <;> simp [Chart.dualMapR])
  refine ⟨φ', he', w', hg'', Chart.dualMapR f', hc.cancel (hc''.congr hsp rfl) hw0,
    (isGen_iff w').2 (T.pgen_cancel t.PP.isLB g g''),
    (maps_iff w' _ (fun _ => eSec t'.G) _ x.rig t'.PP.rig (spMap f') _ (rigPull_le φ' (spMap f') he' t'.PP.L)
      (fun _ => rfl)).2 (T.pmaps_cancel t.PP.isLB (fun _ => he') r r''),
    (appLE_eq_iff_stalk w' θ' x.th).2 fun Z q z i k hi hk => ?_, fun a => ?_, ?_, fun i => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart t.PP.isLB (m.φ (φ' (q z)))
    have a := hs Z (q ≫ φ') z j i hj hi
    have b := (appLE_eq_iff_stalk w'' θ x.th).1 hs'' Z q z j k hj hk
    rw [T Z q z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hp.hom_ext
    · rw [Category.assoc, hv'', Category.assoc, hvv, ← hFF, ← Category.assoc, spMap_comp]
    · rw [Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_pat_of_isFibreOf {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {t : SAB H (Sp R)}
    {t' : SAB H (Sp R')} (m : SABMap t' t (spMap f)) {θ : t.PP.L.Sec} {n : ℕ} {v : Fin n → (epsR R ⟶ t.G)}
    {x : KeyIn R'} (hx : IsFibreOf x t.G t.PP.L t.PP.rig θ v f) : ∃ T : GlobalTheory.CM.PAT H (Sp R'), T.t = t' ∧ T.g = x.P.g := by
  obtain ⟨φ, -, w, -, -, hc, hw, -⟩ := hx
  obtain ⟨w'', hw'', -⟩ := m.lin
  obtain ⟨ψ, hψ, hψ₀⟩ : ∃ ψ : t'.G.left ⟶ x.P.A.left, ψ ≫ φ = m.φ ∧ ψ ≫ x.P.A.hom = t'.G.hom ≫ 𝟙 _ :=
    ⟨hc.1.lift m.φ t'.G.hom m.cart.1.w, hc.1.lift_fst _ _ _, (hc.1.lift_snd _ _ _).trans (Category.comp_id _).symm⟩
  have hp : IsGrpPullback t'.G x.P.A (𝟙 _) ψ := hc.cancel (m.cart.congr (Category.id_comp _).symm hψ.symm) hψ₀
  have e : LBIso t'.PP.L (x.P.L.pull ψ) := by
    have key : ∀ (χ : t'.G.left ⟶ t.G.left) (_ : ψ ≫ φ = χ) (u : LB.Iso t'.PP.L (t.PP.L.pull χ)), u.IsGen →
        LBIso t'.PP.L (x.P.L.pull ψ) := by
      rintro _ rfl u hu
      have g := (isGen_iff w).1 hw
      have g'' := (isGen_iff u).1 hu
      obtain ⟨w', T⟩ := exists_cancel t.PP.isLB w u g g'' x.P.isLB t'.PP.isLB
      exact ⟨w', (isGen_iff w').2 (T.pgen_cancel t.PP.isLB g g'')⟩
    exact key _ hψ w'' hw''
  obtain ⟨h₁, h₂, h₃⟩ := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally _ _ x.P.A t'.G _ ψ
    x.P.L t'.PP.L x.P.isLB t'.PP.isLB x.P.isAb hp e
  have hs : Out.Sym t'.G t'.PP.L := by
    obtain ⟨-, w, hw, -⟩ := t'.sym
    exact fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff w).1 hw) _⟩
  have hd : SmoothOfRelativeDimension x.P.g t'.G.hom :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} x.P.g
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension x.P.g) hp.1 x.P.smoothDim
  exact ⟨⟨t', h₁, x.P.g, hd, hs, h₂ x.P.ample, h₃ x.P.ktriv⟩, rfl, rfl⟩

theorem nonzeroClosed_of_primitive {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {G : Over (Sp V)}
    [Smooth G.hom] {L : LB G.left} (θ : L.Sec)
    (h : ∀ (d : V) (θ' : L.Sec), (∀ i, θ.f i = constFn G.hom _ d * θ'.f i) → IsUnit d) : NonzeroClosed (X := G) θ := by
  by_contra hn
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hred : IsReduced (pullback G.hom (Spec.map (CommRingCat.ofHom (residue V)))) :=
    isReduced_of_smooth (pullback.snd G.hom (spMap (residue V)))
  obtain ⟨σ, hσ⟩ := DVR.exists_div_sec_of_thick G.hom (maximalIdeal V) hϖ.ne_zero hϖ.maximalIdeal_eq.le θ
    (fun j z hz => by
      have : IsReduced (pullback G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal V))))) := hred
      have z₀ : ((pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal V))))).app
          (L.U j)).hom (θ.f j) = 0 := by
        rw [← basicOpen_eq_bot_iff, eq_bot_iff]
        intro y hy
        rw [← Scheme.preimage_basicOpen] at hy
        refine (hn ⟨_, ?_, TopologicalSpace.Opens.mem_iSup.2 ⟨j, hy⟩⟩).elim
        exact (congrArg (fun q : pullback G.hom (spMap (residue V)) ⟶ Sp V => q y) pullback.condition).trans
          (PrimeSpectrum.comap_residue V _)
      rw [gs_eq _ _ _ hz, z₀, map_zero]
      exact dvd_zero _)
  exact hϖ.not_isUnit (h ϖ σ hσ)

end PositivityTheory.HtPt.Kftwo
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MiTors
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.BT.Tors ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

namespace PositivityTheory.HtPt.Mi

section Cat
universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]

omit [BraidedCategory C] in

theorem isMonHom_of_mul {A B : C} [GrpObj A] [GrpObj B] (j : A ⟶ B)
    (h : ∀ (Y : C) (y z : Y ⟶ A), (y * z) ≫ j = (y ≫ j) * (z ≫ j)) : IsMonHom j := by
  constructor
  · have h1 := h (𝟙_ C) 1 1
    rw [_root_.mul_one] at h1
    have h2 : (1 : 𝟙_ C ⟶ A) ≫ j = 1 := by
      have := h1
      exact (left_eq_mul.1 this)
    simpa [Hom.one_def] using h2
  · have h1 := h (A ⊗ A) (fst A A) (snd A A)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h1
    rw [h1]
    congr 1
    ext <;> simp

theorem isPullback_of_kernel {A B : C} [GrpObj B] [IsCommMonObj B] {N : ℕ} (j : A ⟶ B)
    (inj : ∀ (Y : C) (y z : Y ⟶ A), y ≫ j = z ≫ j → y = z)
    (ker : ∀ (Y : C) (g : Y ⟶ B), g ^ N = 1 ↔ ∃ y : Y ⟶ A, y ≫ j = g) :
    IsPullback j (toUnit A) ((𝟙 B) ^ N) η[B] := by
  have hw : j ≫ (𝟙 B) ^ N = toUnit A ≫ η[B] := by
    rw [comp_pow_id, (ker A j).2 ⟨𝟙 _, Category.id_comp _⟩, Hom.one_def]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => ((ker _ s.fst).1 ?_).choose) (fun s => ?_) (fun s => ?_)
    (fun s m h1 _ => ?_)⟩⟩
  · rw [← comp_pow_id s.fst, Hom.one_def, ← toUnit_unique s.snd (toUnit _)]
    exact s.condition
  · exact Exists.choose_spec (p := fun y => y ≫ j = s.fst) _
  · exact toUnit_unique _ _
  · apply inj
    rw [h1]
    exact (Exists.choose_spec (p := fun y => y ≫ j = s.fst) _).symm

omit [BraidedCategory C] in
theorem pow_comp {Y A B : C} [GrpObj A] [GrpObj B] (g : Y ⟶ A) (a : A ⟶ B) [IsMonHom a] (n : ℕ) :
    (g ^ n) ≫ a = (g ≫ a) ^ n := by
  induction n with
  | zero => simp [MonObj.one_comp]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

end Cat

section Tors
variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] {Γ : QFGroup R T} {S : Scheme.{0}}
  {G : Over S} [GrpObj G] [IsCommMonObj G] {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left}

theorem kernel_of_tors (h : Γ.IsTorsionAlong G x N i) :
    ∃ j : Γ.G ⟶ (Over.pullback x).obj G, j.left ≫ pullback.fst G.hom x = i ∧
      IsPullback j (toUnit Γ.G) ((𝟙 ((Over.pullback x).obj G)) ^ N) η[(Over.pullback x).obj G] := by
  let g : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
  have hj : (toPull x G g).left ≫ pullback.fst G.hom x = i := toPull_fst x G g
  refine ⟨toPull x G g, hj, isPullback_of_kernel _ (fun Y y z e => h.inj Y y z ?_) (fun Y c => ?_)⟩
  · rw [← hj, ← Category.assoc, ← Category.assoc, ← Over.comp_left, e, Over.comp_left]
  · have h1 : c ^ N = 1 ↔ ofPull x G c ^ N = 1 := by
      have h2 := map_pow (toPullHom x G Y) (ofPull x G c) N
      have h3 : toPullHom x G Y (ofPull x G c) = c := toPull_ofPull x G c
      rw [h3] at h2
      rw [← h2]
      constructor
      · intro e
        rw [← map_one (toPullHom x G Y)] at e
        exact toPull_inj e
      · intro e
        rw [e, map_one]
    rw [h1, h.kernel]
    refine exists_congr fun y => ⟨fun e => hom_ext_pull ?_, fun e => ?_⟩
    · rw [Over.comp_left, Category.assoc, hj, e]; rfl
    · rw [← hj, ← Category.assoc, ← Over.comp_left, e]; rfl

end Tors

theorem kernel_isPullback {Z : Scheme.{0}} {A B D : Over Z} [GrpObj D] {j : A ⟶ B} {q : B ⟶ D}
    (hp : IsPullback j (toUnit A) q η[D]) : IsPullback j.left A.hom q.left (η[D]).left := by
  have hl := hp.map (Over.forget Z)
  have hA : (toUnit A).left = A.hom := by simpa using Over.w (toUnit A)
  rw [← hA]; exact hl

theorem isClosedImmersion_unit {Z : Scheme.{0}} (B : Over Z) [GrpObj B] [IsSeparated B.hom] :
    IsClosedImmersion (η[B]).left := by
  have : IsClosedImmersion ((η[B]).left ≫ B.hom) := by
    have : (η[B]).left ≫ B.hom = 𝟙 _ := by simpa using Over.w η[B]
    rw [this]; infer_instance
  exact IsClosedImmersion.of_comp _ B.hom

theorem torsion_finite : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → IsProper (pullback.snd G.hom x) → IsFinite Γ.G.hom := by
  intro R _ _ T _ _ Γ S G _ _ x N i h hprop
  obtain ⟨j, -, hp⟩ := kernel_of_tors h
  have : IsProper ((Over.pullback x).obj G).hom := hprop
  have hj : IsClosedImmersion j.left :=
    MorphismProperty.of_isPullback (kernel_isPullback hp).flip (isClosedImmersion_unit _)
  have : IsProper Γ.G.hom := by rw [← Over.w j]; infer_instance
  have := Γ.quasiFinite
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

theorem torsion_etale : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → IsUnit (N : R) → Etale Γ.G.hom := by
  intro R _ _ T _ _ Γ S G _ _ x N i h _ hN
  obtain ⟨j, -, hp⟩ := kernel_of_tors h
  have hN' : IsUnit (N : Γ(Spec (CommRingCat.of R), ⊤)) := by
    simpa using hN.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have e1 : FormallyUnramified ((𝟙 ((Over.pullback x).obj G)) ^ N).left :=
    GlobalTheory.formallyUnramified_mulA _ ((Over.pullback x).obj G) N hN'
  have : FormallyUnramified Γ.G.hom := MorphismProperty.of_isPullback (kernel_isPullback hp) e1
  have := Γ.flat
  have := Γ.finPres
  exact Etale.of_formallyUnramified_of_flat _

theorem torsion_end : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (a : G ⟶ G) [IsMonHom a], ∃ a' : Γ.G ⟶ Γ.G, IsMonHom a' ∧ a'.left ≫ i = i ≫ a.left := by
  intro R _ _ T _ _ Γ S G _ _ x N i h a _
  let g : Over.mk (Γ.G.hom ≫ x) ⟶ G := Over.homMk i h.isOver
  have hg : g ^ N = 1 := (h.kernel Γ.G g).2 ⟨𝟙 _, Category.id_comp _⟩
  have hga : (g ≫ a) ^ N = 1 := by rw [← pow_comp, hg, MonObj.one_comp]
  obtain ⟨a', ha'⟩ := (h.kernel Γ.G (g ≫ a)).1 hga
  replace ha' : a'.left ≫ i = i ≫ a.left := ha'
  refine ⟨a', isMonHom_of_mul _ fun Y y z => h.inj Y _ _ ?_, ha'⟩
  let p : (Y ⟶ Γ.G) → (Over.mk (Y.hom ≫ x) ⟶ G) := fun y => Over.homMk (y.left ≫ i) (by
    simp only [Over.mk_hom, Category.assoc, h.isOver]; rw [← Category.assoc, Over.w])
  have hp : ∀ y, (p y).left = y.left ≫ i := fun _ => rfl
  have hpa : ∀ y, (p y ≫ a).left = (y ≫ a').left ≫ i := fun y => by
    rw [Over.comp_left, Over.comp_left, hp, Category.assoc, Category.assoc, ha']
  rw [← h.mul Y _ _ _ _ (hpa y) (hpa z), ← MonObj.mul_comp, Over.comp_left, Over.comp_left,
    h.mul Y _ _ _ _ (hp y) (hp z), Category.assoc, Category.assoc, ha']

end PositivityTheory.HtPt.Mi
end
end

