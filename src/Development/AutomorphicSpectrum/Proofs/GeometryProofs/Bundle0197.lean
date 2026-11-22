import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0112
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0172
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0190
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0127
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0189
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0108
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0126
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0167
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0120
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0128
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeOnPuncturedDisc
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0185

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricFrameProjectionAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

theorem spec_dual_fst {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom B B B).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualMap φ)) =
      Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  simp [dualMap]

theorem tan_of_lieVal {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {M : LieModel G ξ Li} {z : Sp ℂ ⟶ X} {e : Li}
    {w : epsAt z ⟶ G} (h : M.ValAt z e w) : IsTanAt G z w := by
  obtain ⟨hz, v, ⟨hv, -⟩, hw⟩ := h
  unfold IsTanAt at hv ⊢
  let t : Over.mk z ⟶ Over.mk (X.fromSpecStalk (centre z)) :=
    Over.homMk (Spec.map (Scheme.stalkClosedPointTo z)) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z)
  have h1 : t ≫ (1 : Over.mk (X.fromSpecStalk (centre z)) ⟶ G) = 1 := MonObj.comp_one t
  have h2 := congrArg CommaMorphism.left h1
  rw [hw]
  refine Eq.trans ?_ h2
  change _ = Spec.map (Scheme.stalkClosedPointTo z) ≫ (1 : Over.mk (X.fromSpecStalk (centre z)) ⟶ G).left
  refine Eq.trans ?_ (congrArg (fun k => Spec.map (Scheme.stalkClosedPointTo z) ≫ k) hv)
  have key := spec_dual_fst (Scheme.stalkClosedPointTo z).hom
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ v.left) key).trans (Category.assoc _ _ _))

theorem eq_sum_of_mem_flagStep {Ω : Type} [Field Ω] {Li : Type} [AddCommGroup Li] [Module Ω Li] {r n : ℕ}
    (hn : n ≤ r) (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li) (hd : ∀ j l, π j (b l) = if j = l then 1 else 0)
    {w : Li} (hw : w ∈ flagStep Ω b n) :
    w = ∑ l : Fin n, π (Fin.castLE hn l) w • b (Fin.castLE hn l) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    have hk' : (k : ℕ) < n := hk
    rw [Finset.sum_eq_single (⟨k, hk'⟩ : Fin n)]
    · simp [hd, Fin.castLE]
    · intro l _ hl
      have : Fin.castLE hn l ≠ k := fun e => hl (Fin.ext (by simpa using congrArg Fin.val e))
      simp [hd, this]
    · simp
  | zero => simp
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    simp [add_smul, Finset.sum_add_distrib]
  | smul a x _ hx =>
    conv_lhs => rw [hx]
    simp [Finset.smul_sum, mul_smul]

theorem ev_sum {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {z : Sp ℂ ⟶ X} {p : Cpt ξ}
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {L : Submodule (regAt ξ p) Li} {V : Type} [AddCommGroup V]
    [Module ℂ V] (ev : L →+ V)
    (hev : ∀ (a : regAt ξ p) (r : ℂ) e, ValAt ξ z (a : Ω) r → ev (a • e) = r • ev e) {n : ℕ} (g : Fin n → Li)
    (hg : ∀ l, g l ∈ L) (a : Fin n → Ω) (ha : ∀ l, a l ∈ regAt ξ p) (c : Fin n → ℂ)
    (hc : ∀ l, ValAt ξ z (a l) (c l)) {w : Li} (hw : w ∈ L) (hwe : w = ∑ l, a l • g l) :
    ev ⟨w, hw⟩ = ∑ l, c l • ev ⟨g l, hg l⟩ := by
  have h1 : (⟨w, hw⟩ : L) = ∑ l, (⟨a l, ha l⟩ : regAt ξ p) • (⟨g l, hg l⟩ : L) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact hwe
  rw [h1, map_sum]
  exact Finset.sum_congr rfl fun l _ => hev _ _ _ (hc l)

theorem gram_val : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y) (z : Sp ℂ ⟶ X)
    (hz : genPt ξ ⤳ centre z) (r : ℕ) (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li)
    (B : Fin r → (epsAt z ⟶ G)) (i : Fin r), IsCptGen ξ → (∀ j l, π j (b l) = if j = l then 1 else 0) →
    (∀ j, ∀ e ∈ M.lat ⟨centre z, hz⟩, π j e ∈ regAt ξ ⟨centre z, hz⟩) → (∀ j, M.ValAt z (b j) (B j)) →
    ∀ (f : Fin i → Li) (e : Li) (v : Fin i → (epsAt z ⟶ G)) (ve : epsAt z ⟶ G) (s : ℂ),
      (∀ j, f j ∈ flagStep Ω b i) → e ∈ flagStep Ω b (i + 1) → (∀ j, M.ValAt z (f j) (v j)) → M.ValAt z e ve →
      ValAt ξ z (π i e) s → s ≠ 0 → (gramAt h z v).det ≠ 0 →
      (1 / 2) * (Real.log ‖(gramAt h z (Fin.snoc v ve : Fin (i + 1) → (epsAt z ⟶ G))).det‖ -
          Real.log ‖(gramAt h z v).det‖) =
        Real.log ‖s‖ + (1 / 2) * (Real.log ‖(gramAt h z fun l : Fin (i + 1) => B (Fin.castLE i.2 l)).det‖ -
          Real.log ‖(gramAt h z fun l : Fin i => B (Fin.castLE i.2.le l)).det‖) := by
  intro X Ω _ ξ K J y G _ _ _ Li _ _ M h z hz r b π B i hξ hd hreg hB f e v ve s hf he hv hve hs hs0 hdet
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists X G ℂ z
  obtain ⟨ev, hev1, hev2, -⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ Li M ℂ z hz Vz MR hξ inferInstance
  obtain ⟨core, hcore⟩ := h.herm z Vz MR
  have val : ∀ {e' : Li} {w : epsAt z ⟶ G}, M.ValAt z e' w →
      ∃ he' : e' ∈ M.lat ⟨centre z, hz⟩, MR.pt (ev ⟨e', he'⟩) = w := by
    intro e' w hw
    obtain ⟨x, rfl⟩ := MR.onto w (tan_of_lieVal hw)
    obtain ⟨he', hx⟩ := (hev1 e' x).1 hw
    exact ⟨he', by rw [hx]⟩
  choose hbL hbB using fun j => val (hB j)
  choose hfL hfv using fun j => val (hv j)
  obtain ⟨heL, hve'⟩ := val hve
  obtain ⟨β, hβ⟩ : ∃ β : Fin (i + 1) → Vz, ∀ l, β l = ev ⟨b (Fin.castLE i.2 l), hbL _⟩ := ⟨_, fun _ => rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : Fin i → Vz, ∀ j, x j = ev ⟨f j, hfL j⟩ := ⟨_, fun _ => rfl⟩
  obtain ⟨xe, hxe⟩ : ∃ xe : Vz, xe = ev ⟨e, heL⟩ := ⟨_, rfl⟩
  have hi : (i : ℕ) ≤ r := i.2.le
  have hC : ∀ (j : Fin i) (l : Fin r), ∃ c : ℂ, ValAt ξ z (π l (f j)) c :=
    fun j l => val_exists (hreg l _ (hfL j))
  choose C hC using hC
  have hD : ∀ l : Fin r, ∃ c : ℂ, ValAt ξ z (π l e) c := fun l => val_exists (hreg l _ heL)
  choose D hD using hD
  have hsD : D i = s := val_unique hξ (hD i) hs
  have hsum : ∀ j, x j = ∑ l : Fin i, C j (Fin.castLE hi l) • β l.castSucc := by
    intro j
    rw [hx j, ev_sum ev hev2 (fun l : Fin i => b (Fin.castLE hi l)) (fun _ => hbL _)
      (fun l => π (Fin.castLE hi l) (f j)) (fun _ => hreg _ _ (hfL j)) (fun l => C j (Fin.castLE hi l))
      (fun _ => hC _ _) (hfL j) (eq_sum_of_mem_flagStep hi b π hd (hf j))]
    exact Finset.sum_congr rfl fun l _ => by rw [hβ]; rfl
  have hsume : xe = ∑ l : Fin i, D (Fin.castLE hi l) • β l.castSucc + s • β (Fin.last i) := by
    rw [hxe, ev_sum ev hev2 (fun l : Fin (i + 1) => b (Fin.castLE i.2 l)) (fun _ => hbL _)
      (fun l => π (Fin.castLE i.2 l) e) (fun _ => hreg _ _ heL) (fun l => D (Fin.castLE i.2 l))
      (fun _ => hD _) heL (eq_sum_of_mem_flagStep i.2 b π hd he), Fin.sum_univ_castSucc]
    congr 1
    · exact Finset.sum_congr rfl fun l _ => by rw [hβ]; rfl
    · rw [hβ, ← hsD]; rfl
  have gr : ∀ {m : ℕ} (u : Fin m → Vz),
      gramAt h z (fun l => MR.pt (u l)) = Matrix.of fun a b => core.inner (u a) (u b) := by
    intro m u
    ext a c
    simp [gramAt, hcore]
  have e1 : v = fun l => MR.pt (x l) := funext fun j => by rw [hx, hfv]
  have e2 : (Fin.snoc v ve : Fin (i + 1) → (epsAt z ⟶ G)) =
      fun l => MR.pt ((Fin.snoc x xe : Fin (i + 1) → Vz) l) := by
    funext l
    refine Fin.lastCases ?_ (fun l => ?_) l
    · simp [hxe, hve']
    · simp [e1]
  have e3 : (fun l : Fin (i + 1) => B (Fin.castLE i.2 l)) = fun l => MR.pt (β l) :=
    funext fun l => by rw [hβ, hbB]
  have e4 : (fun l : Fin i => B (Fin.castLE i.2.le l)) = fun l => MR.pt (β l.castSucc) :=
    funext fun l => by rw [hβ, hbB]; rfl
  have hind := GlobalTheory.T.gramAt_det_ne_zero_of_dual_frame X Ω ξ K J y G Li M h z hz r b π B hξ hd hreg hB (i + 1) (Fin.castLE i.2)
    (Fin.castLE_injective _)
  change (gramAt h z fun l : Fin (i + 1) => B (Fin.castLE i.2 l)).det ≠ 0 at hind
  rw [e3, gr] at hind
  rw [e1, gr] at hdet
  rw [e2, e3, e4, e1, gr, gr, gr, gr]
  exact GlobalTheory.T.gram_det_change_of_basis Vz core i β x xe (Matrix.of fun j l => C j (Fin.castLE hi l))
    (fun l => D (Fin.castLE hi l)) s hsum hsume hs0 hdet hind

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeIsoCompat
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GMove

section Ring

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

theorem dualMap_algebraMap (f : R →+* S) :
    (dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap S (DualNumber S)).comp f := by
  ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fstHom_dualMap (f : R →+* S) :
    (TrivSqZeroExt.fstHom S S S).toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom :=
  RingHom.ext fun x => by simp [dualMap]

theorem dualMap_comp (f : R →+* S) (g : S →+* T) : dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  ext x <;> simp [dualMap]

theorem specMap_comp (f : R →+* S) (g : S →+* T) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom (g.comp f)) := by
  rw [← Spec.map_comp]; rfl

end Ring

section Scheme

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω]

theorem specializes_of_iso (e : X' ≅ X) {a b : X'} (h : e.hom a ⤳ e.hom b) : a ⤳ b := by
  have := h.map e.inv.continuous
  simpa using this

theorem genMap_stalkMap_eq (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (q : Cpt ξ')
    (h : genPt (ξ' ≫ g) ⤳ g q.1) (s : X.presheaf.stalk (g q.1)) :
    genMap ξ' q ((g.stalkMap q.1).hom s) = genMap (ξ' ≫ g) ⟨g q.1, h⟩ s := by
  have e := Scheme.Hom.stalkSpecializes_stalkMap g _ _ q.2
  have e2 := congrArg (fun t => (t ≫ Scheme.stalkClosedPointTo ξ').hom s) e
  have e3 := Scheme.stalkClosedPointTo_comp ξ' g
  have e4 := congrArg (fun t => (X.presheaf.stalkSpecializes h ≫ t).hom s) e3
  exact e2.symm.trans e4.symm

theorem eta_comp {G : Over X} [GrpObj G] {G' : Over X'} [GrpObj G'] (f : X' ⟶ X) (φ : G'.left ⟶ G.left)
    (h : IsGrpPullback G' G f φ) : η[G'].left ≫ φ = f ≫ η[G].left := by
  have hw := h.1.w
  let x₀ : Over.mk ((Over.mk (𝟙 X')).hom ≫ f) ⟶ G :=
    Over.homMk ((1 : Over.mk (𝟙 X') ⟶ G').left ≫ φ) (by
      rw [Category.assoc, hw, ← Category.assoc, Over.w]; simp)
  have hm := h.2 (Over.mk (𝟙 X')) 1 1 x₀ x₀ rfl rfl
  have hx : x₀ * x₀ = x₀ := by
    ext1
    rw [hm, _root_.mul_one]
    rfl
  have h1 : x₀ = 1 := by simpa using hx
  have h2 := congrArg (fun u => u.left) h1
  simpa [x₀, Hom.one_def] using h2

end Scheme

section Move

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]

theorem valAt_up (e : X' ≅ X) {G : Over X} [GrpObj G] {G' : Over X'} [GrpObj G'] (φ : G'.left ≅ G.left)
    (hw : φ.hom ≫ G.hom = G'.hom ≫ e.hom) (hη : η[G'].left ≫ φ.hom = e.hom ≫ η[G].left)
    {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω ⟶ X'} (M : LieModel G ξ V) (M' : LieModel G' ξ' V) (hξ : ξ' ≫ e.hom = ξ)
    (hpt : ∀ v, (M'.pt v).left ≫ φ.hom = (M.pt v).left)
    {z : Sp ℂ ⟶ X'} {z₀ : Sp ℂ ⟶ X} (hz : z ≫ e.hom = z₀) {b : V} {w : epsAt z₀ ⟶ G} {w' : epsAt z ⟶ G'}
    (hww : w'.left ≫ φ.hom = w.left) : M.ValAt z₀ b w → M'.ValAt z b w' := by
  subst hξ hz
  rintro ⟨h, v, ⟨hvt, hve⟩, hvw⟩
  have h' : genPt ξ' ⤳ centre z := specializes_of_iso e h
  change e.hom (genPt ξ') ⤳ e.hom (centre z) at h
  change epsAt (R := X.presheaf.stalk (e.hom (centre z))) (X.fromSpecStalk (e.hom (centre z))) ⟶ G at v
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk (e.hom (centre z)))
      (X.presheaf.stalk (e.hom (centre z))) (X.presheaf.stalk (e.hom (centre z)))).toRingHom) ≫ v.left =
      (1 : Over.mk (X.fromSpecStalk (e.hom (centre z))) ⟶ G).left at hvt
  change (M.pt b).left = Spec.map (CommRingCat.ofHom (dualMap (genMap (ξ' ≫ e.hom) ⟨e.hom (centre z), h⟩))) ≫
      v.left at hve
  change w.left = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo (z ≫ e.hom)).hom)) ≫ v.left at hvw
  have hφ : φ.inv ≫ G'.hom = G.hom ≫ e.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hw, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hη' : e.hom ≫ η[G].left ≫ φ.inv = η[G'].left := by
    rw [← Category.assoc, ← hη, Category.assoc, φ.hom_inv_id, Category.comp_id]
  have hv : v.left ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (e.hom (centre z)))
      (DualNumber (X.presheaf.stalk (e.hom (centre z)))))) ≫ X.fromSpecStalk (e.hom (centre z)) := Over.w v
  have hσ : Spec.map (e.hom.stalkMap (centre z)) ≫ X.fromSpecStalk (e.hom (centre z)) =
      X'.fromSpecStalk (centre z) ≫ e.hom := Scheme.SpecMap_stalkMap_fromSpecStalk e.hom
  have k1 : Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (e.hom (centre z)))
        (DualNumber (X.presheaf.stalk (e.hom (centre z)))))) =
      Spec.map (CommRingCat.ofHom (algebraMap (X'.presheaf.stalk (centre z))
        (DualNumber (X'.presheaf.stalk (centre z))))) ≫ Spec.map (e.hom.stalkMap (centre z)) := by
    rw [specMap_comp, dualMap_algebraMap, ← specMap_comp]
    rfl
  let v' : epsAt (R := X'.presheaf.stalk (centre z)) (X'.fromSpecStalk (centre z)) ⟶ G' :=
    Over.homMk (Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) ≫ v.left ≫ φ.inv) (by
      show _ ≫ (v.left ≫ φ.inv) ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap (X'.presheaf.stalk (centre z))
        (DualNumber (X'.presheaf.stalk (centre z))))) ≫ X'.fromSpecStalk (centre z)
      rw [Category.assoc, hφ, reassoc_of% hv]
      show Spec.map _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (e.hom (centre z)))
        (DualNumber (X.presheaf.stalk (e.hom (centre z)))))) ≫ X.fromSpecStalk (e.hom (centre z))) ≫ e.inv = _
      rw [← Category.assoc, ← Category.assoc]
      erw [k1]
      erw [Category.assoc, Category.assoc, reassoc_of% hσ, e.hom_inv_id, Category.comp_id]
      rfl)
  have hv' : v'.left = Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) ≫ v.left ≫ φ.inv := rfl
  refine ⟨h', v', ⟨?_, ?_⟩, ?_⟩
  · have e1 : (1 : Over.mk (X'.fromSpecStalk (centre z)) ⟶ G').left = X'.fromSpecStalk (centre z) ≫ η[G'].left := by
      simp [Hom.one_def]
    have e2 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk (e.hom (centre z)))
        (X.presheaf.stalk (e.hom (centre z))) (X.presheaf.stalk (e.hom (centre z)))).toRingHom) ≫ v.left =
        X.fromSpecStalk (e.hom (centre z)) ≫ η[G].left := by
      rw [hvt]
      simp [Hom.one_def]
    have k2 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X'.presheaf.stalk (centre z))
        (X'.presheaf.stalk (centre z)) (X'.presheaf.stalk (centre z))).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) =
        Spec.map (e.hom.stalkMap (centre z)) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom
        (X.presheaf.stalk (e.hom (centre z))) (X.presheaf.stalk (e.hom (centre z)))
        (X.presheaf.stalk (e.hom (centre z)))).toRingHom) := by
      rw [specMap_comp, fstHom_dualMap, ← specMap_comp]
      rfl
    show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X'.presheaf.stalk (centre z))
        (X'.presheaf.stalk (centre z)) (X'.presheaf.stalk (centre z))).toRingHom) ≫ v'.left =
        (1 : Over.mk (X'.fromSpecStalk (centre z)) ⟶ G').left
    rw [hv', e1, ← hη', ← reassoc_of% hσ, ← reassoc_of% e2, reassoc_of% k2]
    rfl
  · have k3 : Spec.map (CommRingCat.ofHom (dualMap (genMap ξ' ⟨centre z, h'⟩))) ≫
        Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) =
        Spec.map (CommRingCat.ofHom (dualMap (genMap (ξ' ≫ e.hom) ⟨e.hom (centre z), h⟩))) := by
      have hg : (genMap ξ' ⟨centre z, h'⟩).comp (e.hom.stalkMap (centre z)).hom =
          genMap (ξ' ≫ e.hom) ⟨e.hom (centre z), h⟩ :=
        RingHom.ext (genMap_stalkMap_eq ξ' e.hom ⟨centre z, h'⟩ h)
      rw [specMap_comp, ← dualMap_comp, hg]
    show (M'.pt b).left = Spec.map (CommRingCat.ofHom (dualMap (genMap ξ' ⟨centre z, h'⟩))) ≫ v'.left
    rw [(Iso.eq_comp_inv φ).2 (hpt b), hve, hv', reassoc_of% k3]
    exact Category.assoc _ _ _
  · have k4 : Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫
        Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) =
        Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo (z ≫ e.hom)).hom)) := by
      refine (specMap_comp (dualMap (e.hom.stalkMap (centre z)).hom) (dualMap (Scheme.stalkClosedPointTo z).hom)).trans ?_
      rw [Scheme.stalkClosedPointTo_comp]
      exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (dualMap_comp _ _).symm
    rw [(Iso.eq_comp_inv φ).2 hww, hvw, hv', ← k4]
    erw [Category.assoc, Category.assoc]

end Move

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem gramAt_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (e : X' ≅ X)
    (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (k : SABMap t' t e.hom)
    (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V),
    ξ' ≫ e.hom = ξ → (∀ v, (M'.pt v).left ≫ k.φ = (M.pt v).left) →
    ∀ (z : Sp ℂ ⟶ X') (r : ℕ) (b : Fin r → V) (Γ : Matrix (Fin r) (Fin r) ℂ),
      M'.GramAt t'.PP.L z b Γ ↔ M.GramAt t.PP.L (z ≫ e.hom) b Γ := by
  intro E _ _ _ H X X' e Ω _ ξ ξ' t t' k V _ _ M M' hξ hpt z r b Γ
  haveI : IsIso k.φ := k.cart.1.isIso_fst_of_isIso
  let φ : t'.G.left ≅ t.G.left := asIso k.φ
  have hw : φ.hom ≫ t.G.hom = t'.G.hom ≫ e.hom := k.cart.1.w
  have hη : η[t'.G].left ≫ φ.hom = e.hom ≫ η[t.G].left := eta_comp e.hom k.φ k.cart
  have hw' : φ.symm.hom ≫ t'.G.hom = t.G.hom ≫ e.symm.hom := by
    show φ.inv ≫ _ = _ ≫ e.inv
    rw [Iso.inv_comp_eq, ← Category.assoc, hw, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hη' : η[t.G].left ≫ φ.symm.hom = e.symm.hom ≫ η[t'.G].left := by
    show _ ≫ φ.inv = e.inv ≫ _
    rw [Iso.eq_inv_comp, ← reassoc_of% hη, φ.hom_inv_id, Category.comp_id]
  have hpt' : ∀ v, (M.pt v).left ≫ φ.symm.hom = (M'.pt v).left := fun v => by
    show _ ≫ φ.inv = _
    rw [← hpt v, Category.assoc]
    erw [φ.hom_inv_id]
    exact Category.comp_id _
  have hξ' : ξ ≫ e.symm.hom = ξ' := by rw [← hξ]; simp
  constructor
  · rintro ⟨v', hval, hip⟩
    let v : Fin r → (epsAt (z ≫ e.hom) ⟶ t.G) := fun i => Over.homMk ((v' i).left ≫ k.φ) (by
      have h1 := Over.w (v' i)
      rw [Category.assoc, k.cart.1.w, ← Category.assoc, h1]
      simp [epsAt])
    refine ⟨v, fun i => ?_, fun p q => ?_⟩
    · refine valAt_up e.symm φ.symm hw' hη' M' M hξ' hpt' (z := z ≫ e.hom) (z₀ := z) (by simp) ?_ (hval i)
      show ((v' i).left ≫ k.φ) ≫ φ.inv = _
      simp [φ]
    · exact (GlobalTheory.T.hodge_inner_product_pullback_iff E H X X' t t' e.hom k z (v' p) (v' q) (v p) (v q) (Γ p q) rfl rfl).1 (hip p q)
  · rintro ⟨v, hval, hip⟩
    let v' : Fin r → (epsAt z ⟶ t'.G) := fun i => Over.homMk ((v i).left ≫ φ.inv) (by
      have h1 := Over.w (v i)
      rw [Category.assoc, ← Iso.symm_hom, hw', ← Category.assoc, h1]
      simp [epsAt])
    have hv' : ∀ i, (v' i).left ≫ k.φ = (v i).left := fun i => by
      show ((v i).left ≫ φ.inv) ≫ φ.hom = _
      simp
    refine ⟨v', fun i => ?_, fun p q => ?_⟩
    · exact valAt_up e φ hw hη M M' hξ hpt (z := z) (z₀ := z ≫ e.hom) rfl (hv' i) (hval i)
    · exact (GlobalTheory.T.hodge_inner_product_pullback_iff E H X X' t t' e.hom k z (v' p) (v' q) (v p) (v q) (Γ p q) (hv' p) (hv' q)).2 (hip p q)

end GlobalTheory.CompanionTheory.Ar.GMove
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrthogonalMetricFlagDegree
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

theorem flagStep_mono' {Ω E' : Type} [Field Ω] [AddCommGroup E'] [Module Ω E'] {r : ℕ} (b : Fin r → E') {i i' : ℕ} (h : i ≤ i') :
    flagStep Ω b i ≤ flagStep Ω b i' :=
  Submodule.span_mono (Set.image_mono fun _ hk => lt_of_lt_of_le hk h)

theorem exists_satFlag {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {L : Type} [Field L] [NumberField L] (M : LieModel G ξ Li)
    (z : Sp (𝓞 L) ⟶ X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier) {r : ℕ}
    (b : Fin r → Li) (hr : ∀ i : ℕ, i ≤ r → Module.finrank (𝓞 L) (subFib M (flagStep Ω b i) z MB) = i) :
    ∃ A : SatFlag B r, ∀ i, A.F i = subFib M (flagStep Ω b i.val) z MB :=
  ⟨{ F := fun i => subFib M (flagStep Ω b i.val) z MB
     mono := fun _ _ hi => subFib_mono M (flagStep_mono' b (Fin.le_def.1 hi)) z MB
     sat := fun _ => subFib_saturated M _ z B MB
     rank := fun i => hr i.val (Nat.lt_succ_iff.1 i.2) }, fun _ => rfl⟩

theorem rank_fib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier),
    Fintype.card (CMType H) * (D.p + D.q) = Module.finrank (𝓞 L) B.carrier ∧
    (∀ s (i : ℕ), i ≤ labelRk D s → Module.finrank (𝓞 L) (subFib 𝔐.M (flagStep Ω (Fl.b s) i) z MB) = i) ∧
    ∀ s (i : ℕ), flagStep Ω (Fl.b s) i ≤ 𝔐.Vgen s := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 _ Fl L _ _ z B MB
  classical
  have hgen : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  haveI hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  have hs : genPt 𝔐.ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z) := 𝔐.all _
  have hu := fun n hn => isUnit_natCast_stalk 𝔐.X L (spMap (algebraMap (𝓞 L) L) ≫ z) n hn
  obtain ⟨b, hb1, hb2, hb3, hb4, hb5, hb6⟩ := GlobalTheory.T.exists_flag_basis_at_stalk E H D l Xo c Y S Ω K J y 𝔐 Fl ⟨_, hs⟩ hu
  obtain ⟨T, _, _, _, _, TL, j, hj, hbc⟩ := GlobalTheory.T.exists_lie_model_base_change 𝔐.X 𝔐.t.G (𝓞 L) L z B.carrier MB
  obtain ⟨w, hw1, hw2, hw3, hw4⟩ := GlobalTheory.T.lie_model_frame_spans_generic 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M L _ T TL hs
    (Σ s, Fin (labelRk D s)) _ hgen hb3 hb4 hb5
  have hbr := fun U => GlobalTheory.T.lie_model_projective_generic_fibre 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M L z B.carrier MB T TL j U hgen hj hbc
  refine ⟨?_, ?_, ?_⟩
  · rw [(hbr ⊥).1]
    have e1 := finrank_span_eq_card hw2
    rw [hw3, finrank_top] at e1
    rw [e1, Fintype.card_sigma, Fintype.sum_sum_type]
    have a1 : ∀ τ : CMType H, Fintype.card (Fin (labelRk D (Sum.inl τ))) = D.p := fun _ => Fintype.card_fin _
    have a2 : ∀ τ : CMType H, Fintype.card (Fin (labelRk D (Sum.inr τ))) = D.q := fun _ => Fintype.card_fin _
    simp only [a1, a2, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  · intro s i hi
    rw [(hbr _).2]
    let g : Fin i → Σ s, Fin (labelRk D s) := fun k => ⟨s, ⟨k.1, lt_of_lt_of_le k.2 hi⟩⟩
    have hg : Function.Injective g := by
      intro a b' hab
      simp only [g, Sigma.mk.injEq, heq_eq_eq, true_and, Fin.mk.injEq] at hab
      exact Fin.ext hab
    have himg : (fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) '' Set.range g = b s '' {k | (k : ℕ) < i} := by
      ext x
      constructor
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨⟨k.1, lt_of_lt_of_le k.2 hi⟩, k.2, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨_, ⟨⟨k.1, hk⟩, rfl⟩, rfl⟩
    have hspan : Submodule.span L {w' | ∃ e ∈ flagStep Ω (Fl.b s) i, 𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w')} =
        Submodule.span L (Set.range (w ∘ g)) := by
      apply le_antisymm
      · refine Submodule.span_le.2 ?_
        rintro w' ⟨e, he, hv⟩
        obtain ⟨h', hl⟩ := (LieModel.exists_valAt_iff 𝔐.M _ e).1 ⟨_, hv⟩
        have h2 := hb2 s i e (by rw [hb1]; exact he) hl
        rw [← himg] at h2
        have := hw4 (Set.range g) e w' h2 hv
        rwa [← Set.range_comp] at this
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨k, rfl⟩
        refine Submodule.subset_span ⟨b s ⟨k.1, lt_of_lt_of_le k.2 hi⟩, ?_, hw1 (g k)⟩
        rw [← hb1]
        exact Submodule.subset_span ⟨_, k.2, rfl⟩
    rw [hspan, finrank_span_eq_card (hw2.comp g hg), Fintype.card_fin]
  · intro s i
    rw [← hb1, ← hb6]
    exact Submodule.span_mono (Set.image_subset_range _ _)

theorem flag_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (h : LieMetric 𝔐.M y), h.Orth 𝔐.t.act → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∃ (A : FlagPair B (CMType H) D.p D.q), A.IsOrthFull ∧ (∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inl τ)) i.val) z MB ((A.W τ).F i)) ∧ ∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inr τ)) i.val) z MB ((A.S τ).F i) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 _ Fl h hO L _ _ z B MB hF
  obtain ⟨h1, h2, h3⟩ := rank_fib E H D l Xo c Y S Ω K J y 𝔐 Fl L z B MB
  have ho := GlobalTheory.T.orthogonal_metric_hermitian_bundle E H D l Xo c Y S Ω K J y 𝔐 h hO L z B MB hF
  have hex : ∀ s, ∃ A : SatFlag B (labelRk D s), ∀ i, A.F i = subFib 𝔐.M (flagStep Ω (Fl.b s) i.val) z MB := by
    intro s
    exact exists_satFlag 𝔐.M z B MB (Fl.b s) (h2 s)
  choose A hA using hex
  have hW : ∀ (τ : CMType H) (i : Fin (D.p + 1)), IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inl τ)) i.val) z MB ((A (.inl τ)).F i) := by
    intro τ i
    rw [hA (.inl τ) i]
    exact isSubFibre_subFib _ _ _ _
  have hS : ∀ (τ : CMType H) (i : Fin (D.q + 1)), IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inr τ)) i.val) z MB ((A (.inr τ)).F i) := by
    intro τ i
    rw [hA (.inr τ) i]
    exact isSubFibre_subFib _ _ _ _
  have hpart : ∀ s, FlagPair.part (⟨fun τ => A (.inl τ), fun τ => A (.inr τ)⟩ : FlagPair B (CMType H) D.p D.q) s =
      subFib 𝔐.M (flagStep Ω (Fl.b s) (labelRk D s)) z MB := by
    rintro (τ | τ)
    · exact hA (.inl τ) (Fin.last _)
    · exact hA (.inr τ) (Fin.last _)
  refine ⟨⟨fun τ => A (.inl τ), fun τ => A (.inr τ)⟩, ⟨?_, h1⟩, hW, hS⟩
  intro a b hab
  rw [hpart, hpart]
  exact ho a b hab _ _ (h3 a _) (h3 b _)

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeOnPuncturedDiscStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_lattice_on_punctured_disc : ∀ (n a g : ℕ) (_h : a ≤ n) (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (E : LinearMap.BilinForm ℤ Λ) (Γ : (Fin n → ℂ) → AddSubgroup (Fin g → ℂ)) (Hf : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (U : Set (Fin n → ℂ)) (Γ₀ : Submodule ℤ (Fin g → ℂ)) (S : Γ₀ → (Fin n → ℂ) → (Fin g → ℂ)), U = {z | z ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ ∀ i : Fin n, i.val < a → z i ≠ 0} → Module.finrank ℤ Λ = 2 * g → (∀ x, E x x = 0) → Function.Bijective E → (∀ z ∈ U, (Hf z).IsHermitian ∧ ∀ x : Fin g → ℂ, x ≠ 0 → 0 < (x ⬝ᵥ Hf z *ᵥ star x).re) → (∀ z₀ ∈ U, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ U ∧ ∃ P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ)), (∀ x, DifferentiableOn ℂ (fun z => P z x) N) ∧ ∀ z ∈ N, Function.Injective (P z) ∧ (P z).range = Γ z ∧ ∀ x y, (P z x ⬝ᵥ Hf z *ᵥ star (P z y)).im = E x y) → (∀ x, DifferentiableOn ℂ (S x) (Metric.ball 0 1) ∧ S x 0 = x ∧ ∀ z ∈ U, S x z ∈ Γ z) → (∀ x y z, S (x + y) z = S x z + S y z) → (∀ s : (Fin n → ℂ) → (Fin g → ℂ), ContinuousAt s 0 → (∀ z ∈ U, s z ∈ Γ z) → s 0 ∈ Γ₀) → Submodule.span ℂ (Γ₀ : Set (Fin g → ℂ)) = ⊤ → (∀ N : ℕ, 0 < N → ∃ T : Set (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))), Nat.card (Γ₀ ⧸ LinearMap.range ((N : ℤ) • (LinearMap.id : Γ₀ →ₗ[ℤ] Γ₀))) * Nat.card T = N ^ (2 * g) ∧ ∀ x y : Γ₀, Submodule.Quotient.mk x ∈ T → ∀ z ∈ U, ∃ k : ℤ, (S x z ⬝ᵥ Hf z *ᵥ star (S y z)).im = N * k) → ∃ L : Flat.LogPeriods n a g Λ, L.H = Hf ∧ ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, (L.P w).range = Γ (GroundTheory.Heights₂.Heights.Regular.expCover a w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_logPeriods_range_eq | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_logPeriods_range_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_logPeriods_range_eq <;> assumption)
end

