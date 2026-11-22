import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3417
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppEqZeroOfValR
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3428
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3123
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2590
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2628
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3419
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieCoordinatesOnFieldFibresLocalRing
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieCoordFibre

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD dualMapR)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem card_eq_of_isLieBasis [Nontrivial R] {n m : ℕ} {v : Fin n → (epsR R ⟶ G)}
    {w : Fin m → (epsR R ⟶ G)} (hv : IsLieBasis v) (hw : IsLieBasis w) : n = m := by
  choose b hb using fun i => LieEigen.exists_prodPts hw (hv.1 i)
  have key : ∀ c, prodPts c v = prodPts (∑ i, c i • b i) w := fun c => by
    rw [← LieEigen.prodPts_prodPts hw.1]
    exact congrArg (prodPts c) (funext fun i => (hb i).symm)
  let L : (Fin n → R) →ₗ[R] (Fin m → R) := Fintype.linearCombination R b
  have hL : ∀ c, L c = ∑ i, c i • b i := fun c => Fintype.linearCombination_apply R b c
  have bij : Function.Bijective L := by
    refine ⟨fun c c' h => LieEigen.prodPts_injective hv ?_, fun d => ?_⟩
    · show prodPts c v = prodPts c' v
      rw [key, key, ← hL, ← hL, h]
    · obtain ⟨c, hc⟩ := LieEigen.exists_prodPts hv (LieEigen.isTangent_prodPts hw.1 d)
      exact ⟨c, LieEigen.prodPts_injective hw (show prodPts (L c) w = prodPts d w by rw [hL, ← key, hc])⟩
  have := (LinearEquiv.ofBijective L bij).finrank_eq
  simpa using this

end GlobalTheory.LieCoordFibre

namespace GlobalTheory.LieCoordFibre

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD dualMapR)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
  {k : Type} [Field k] (f : R →+* k)

theorem push_left (x : epsR k ⟶ (Over.pullback (spMap f)).obj G) :
    (pushHom (isGrpPullback_pullback G (spMap f)) (epsR k) x).left = x.left ≫ pullback.fst G.hom (spMap f) := rfl

theorem push_injective : Function.Injective (pushHom (isGrpPullback_pullback G (spMap f)) (epsR k)) :=
  fun x y e => Over.OverMorphism.ext ((isGrpPullback_pullback G (spMap f)).1.hom_ext
    (congrArg (fun q => q.left) e) ((Over.w x).trans (Over.w y).symm))

theorem push_surjective : Function.Surjective (pushHom (isGrpPullback_pullback G (spMap f)) (epsR k)) := by
  intro w
  have hk := isGrpPullback_pullback G (spMap f)
  refine ⟨Over.homMk (hk.1.lift w.left (epsR k).hom (Over.w w)) (hk.1.lift_snd _ _ _), ?_⟩
  exact Over.OverMorphism.ext (hk.1.lift_fst _ _ _)

theorem unit_fst : η[(Over.pullback (spMap f)).obj G].left ≫ pullback.fst G.hom (spMap f) = spMap f ≫ η[G].left := by
  have e := congrArg (fun q => q.left) (map_one (pushHom (isGrpPullback_pullback G (spMap f)) (𝟙_ (Over (Sp k)))))
  have e₁ : (1 : 𝟙_ (Over (Sp k)) ⟶ (Over.pullback (spMap f)).obj G) = η[(Over.pullback (spMap f)).obj G] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

end GlobalTheory.LieCoordFibre

namespace GlobalTheory.LieCoordFibre

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD dualMapR)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
  {k : Type} [Field k] (f : R →+* k)

theorem isTangent_iff_push (y : epsR k ⟶ (Over.pullback (spMap f)).obj G) :
    IsTangent y ↔ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫
      (pushHom (isGrpPullback_pullback G (spMap f)) (epsR k) y).left = (1 : Over.mk (spMap f) ⟶ G).left := by
  rw [push_left]
  show _ ↔ _ = spMap f ≫ η[G].left
  unfold IsTangent
  constructor
  · intro h
    rw [← Category.assoc, h, unit_fst]
  · intro h
    apply (isGrpPullback_pullback G (spMap f)).1.hom_ext
    · rw [Category.assoc, h, unit_fst]
    · rw [Category.assoc, Over.w y, Over.w η[(Over.pullback (spMap f)).obj G]]
      simp only [Over.mk_hom, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := by
        ext s; simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]
      simp

def scaleAt (a : k) : epsPt (spMap f) ⟶ epsPt (spMap f) :=
  Over.homMk (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD a)).left
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ spMap f) (Over.w (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD a)))))

theorem push_scale (a : k) (y : epsR k ⟶ (Over.pullback (spMap f)).obj G) :
    pushHom (isGrpPullback_pullback G (spMap f)) (epsR k) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD a) ≫ y) =
      scaleAt f a ≫ pushHom (isGrpPullback_pullback G (spMap f)) (epsR k) y :=
  Over.OverMorphism.ext (Category.assoc _ _ _)

end GlobalTheory.LieCoordFibre

namespace GlobalTheory.LieCoordFibre

open ReciprocityTheory.ChartRestriction.G.Chart (prodPts scaleD dualMapR)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}
  {v : Fin n → (epsR R ⟶ G)}

open Classical in

def lieMat (hv : IsLieBasis v) (u : G ⟶ G) : Matrix (Fin n) (Fin n) R :=
  if h : IsMonHom u then Matrix.transpose (haveI := h; (SqZero.existsUnique_lieMatrix u hv.1 hv).exists.choose) else 0

theorem comp_eq_prodPts (hv : IsLieBasis v) (u : G ⟶ G) [IsMonHom u] (j : Fin n) :
    v j ≫ u = prodPts (fun i => lieMat hv u i j) v := by
  have h := (SqZero.existsUnique_lieMatrix u hv.1 hv).exists.choose_spec j
  rw [ReciprocityTheory.ChartRestriction.G.Chart.isLieComb_iff] at h
  rw [lieMat, dif_pos (show IsMonHom u from inferInstance)]
  exact h

end GlobalTheory.LieCoordFibre

open GlobalTheory.LieCoordFibre ReciprocityTheory.ChartRestriction.G.Chart in

theorem GlobalTheory.exists_lie_coordinates_fibres : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∃ (n : ℕ) (M : (G ⟶ G) → Matrix (Fin n) (Fin n) R), (∀ g : ℕ, SmoothOfRelativeDimension g G.hom → n = g) ∧ ∀ (k : Type) [Field k] (f : R →+* k), ∃ T : (Fin n → k) → (epsPt (spMap f) ⟶ G), Function.Injective T ∧ (∀ v : epsPt (spMap f) ⟶ G, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (v).left = (1 : Over.mk (spMap f) ⟶ G).left ↔ v ∈ Set.range T) ∧ (∀ c c', T (c + c') = T c * T c') ∧ (∀ (t : k) c, (T (t • c)).left = spMap (epsScale t) ≫ (T c).left) ∧ ∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map f).mulVec c) := by
  intro R _ _ G _ _ hs
  obtain ⟨n, v, hv⟩ := LieLocalBasis.exists_isLieBasis_of_isLocalRing R G hs
  refine ⟨n, lieMat hv, fun g hg => ?_, fun k _ f => ?_⟩
  · obtain ⟨w, hw⟩ := KeyPow.exists_isLieBasis G hg
    exact card_eq_of_isLieBasis hv hw
  have hk := isGrpPullback_pullback G (spMap f)
  obtain ⟨v', hv', e⟩ := exists_isLieBasis_baseChange R k f G _ _ hk hs n v hv
  let P := pushHom hk (epsR k)
  refine ⟨fun c => P (prodPts c v'), fun c c' h => LieEigen.prodPts_injective hv' (push_injective f h),
    fun w => ?_, fun c c' => ?_, fun t c => ?_, fun u hu c => ?_⟩
  · constructor
    · intro h
      obtain ⟨y, rfl⟩ := push_surjective f w
      obtain ⟨c, rfl⟩ := LieEigen.exists_prodPts hv' ((isTangent_iff_push f y).2 h)
      exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩
      exact (isTangent_iff_push f _).1 (LieEigen.isTangent_prodPts hv'.1 c)
  · show P _ = P _ * P _
    rw [LieEigen.prodPts_add hv'.1, map_mul]
  · show (prodPts (t • c) v').left ≫ _ = _ ≫ (prodPts c v').left ≫ _
    rw [LieEigen.prodPts_smul, Over.comp_left, Category.assoc]
    rfl
  haveI := hu
  let col : Fin n → Fin n → R := fun j i => lieMat hv u i j
  have hz : ∀ j, P (v' j) ≫ u = P (prodPts (f ∘ col j) v') := fun j => Over.OverMorphism.ext (by
    rw [Over.comp_left, push_left, push_left, e j, Category.assoc, ← Over.comp_left,
      comp_eq_prodPts hv u j, ← LieEigen.prodPts_left hk e])
  let Q := (IsMonHom.monoidHom u (epsPt (spMap f))).comp P
  have hQ : ∀ y, Q y = P y ≫ u := fun y => rfl
  have hs' : ∀ j, Q (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (c j)) ≫ v' j) =
      P (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (c j)) ≫ prodPts (f ∘ col j) v') := fun j => by
    rw [hQ, push_scale, push_scale, Category.assoc, hz]
  calc P (prodPts c v') ≫ u = Q (prodPts c v') := rfl
    _ = (List.ofFn fun j => Q (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (c j)) ≫ v' j)).prod := by
      rw [ReciprocityTheory.ChartRestriction.G.Chart.prodPts, map_list_prod, List.map_ofFn]
      rfl
    _ = (List.ofFn fun j => P (ReciprocityTheory.ChartRestriction.G.Chart.spMap (scaleD (c j)) ≫ prodPts (f ∘ col j) v')).prod := by
      simp only [hs']
    _ = P (prodPts c fun j => prodPts (f ∘ col j) v') := by
      rw [ReciprocityTheory.ChartRestriction.G.Chart.prodPts, map_list_prod, List.map_ofFn]
      rfl
    _ = P (prodPts (∑ j, c j • (f ∘ col j)) v') := by rw [LieEigen.prodPts_prodPts hv'.1]
    _ = P (prodPts (((lieMat hv u).map f).mulVec c) v') := by
      congr 2
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, col, mul_comm]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocDerKDesc
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

namespace GlobalTheory.Heat.AbConst

open GlobalTheory.KS.GlueDer

section Ray

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D)

theorem desc_agree (hdd : ∀ a, IsField ⊤ (dd a)) {K : Type} [Field K] [CharZero K] (φ : R →+* K)
    (hΘ : ∀ a b, φ (h.Θ a b) = 0) {Z : Scheme.{0}} (p : Z ⟶ Sp K) (m : Z ⟶ Q.P.A.left)
    (hm : m ≫ Q.P.A.hom = p ≫ spMap φ) (V : h.J → Q.P.A.left.Opens) (hV : ∀ i, h.W i = Y.q.left ⁻¹ᵁ V i)
    (e : h.J → Fld Q.P.A.left)
    (hq : ∀ i V', V' ≤ V i → ∀ f, (Y.q.left.app V').hom (e i V' f) = h.d i _ ((Y.q.left.app V').hom f))
    (i i' : h.J) (W : Q.P.A.left.Opens) (hW : W ≤ V i ⊓ V i') (f : Γ(Q.P.A.left, W)) :
    (m.app W).hom (e i W f) = (m.app W).hom (e i' W f) := by
  have := Y.smooth_q
  have hs := (surjective_q Y).1
  let a := pullback.fst Y.q.left m
  let b := pullback.snd Y.q.left m
  have w : a ≫ Y.q.left = b ≫ m := pullback.condition
  have hle : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ a ⁻¹ᵁ (Y.q.left ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  let π := (a.appLE _ _ hle).hom
  have key : ∀ x, (b.app _).hom ((m.app W).hom x) = π ((Y.q.left.app W).hom x) := fun x => by
    have k : ∀ (c : pullback Y.q.left m ⟶ Q.P.A.left) (_ : c = b ≫ m) (hc : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ c ⁻¹ᵁ W),
        (b.app _).hom ((m.app W).hom x) = (c.appLE W _ hc).hom x := by
      rintro _ rfl hc
      rw [Scheme.Hom.comp_appLE, Scheme.Hom.app_eq_appLE b]
      rfl
    rw [k _ w hle]
    exact congrArg (fun ψ => ψ.hom x) (Scheme.Hom.comp_appLE a Y.q.left W _ hle)
  have hc : ∀ r, π (constFn Y.H.hom _ r) = constFn (b ≫ p) _ (φ r) := fun r => by
    rw [← res_const (b ≫ p) hle, ← app_const φ Y.H.hom (b ≫ p) a (by
      rw [← Over.w Y.q, reassoc_of% w, hm, Category.assoc])]
    rfl
  refine FunDescent.app_injective b _ ?_
  show (b.app _).hom ((m.app W).hom _) = (b.app _).hom ((m.app W).hom _)
  rw [key, key, hq i W (hW.trans inf_le_left), hq i' W (hW.trans inf_le_right)]
  refine lift_agree h hdd i i' _ (le_inf ((pre_mono _ (hW.trans inf_le_left)).trans (hV i).ge)
    ((pre_mono _ (hW.trans inf_le_right)).trans (hV i').ge)) π ?_ (fun a b => ?_) _
  · have := (two_ne_zero (α := K)).isUnit.map ((((b ≫ p).appLE ⊤ (b ⁻¹ᵁ (m ⁻¹ᵁ W)) (fun _ _ => trivial)).hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    rwa [map_ofNat] at this
  · rw [hc, hΘ, constFn, map_zero, map_zero]

end Ray

theorem exists_locDerK_desc : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D), (∀ a, IsField ⊤ (dd a)) → IsBasic Y h → ∀ {K : Type} [Field K] [CharZero K] (φ : R →+* K), (∀ a b, φ (h.Θ a b) = 0) → ∀ {Z : Scheme.{0}} (p : Z ⟶ Sp K) (m : Z ⟶ Q.P.A.left), m ≫ Q.P.A.hom = p ≫ spMap φ → ∃ dl : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(Z, m ⁻¹ᵁ W), GlobalTheory.KS.LocDerK p Q.P.A.hom m (fun r => φ (D r)) ⊤ dl ∧ (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Y.H.left) (b : Z' ⟶ Z), a ≫ Y.q.left = b ≫ m → ∀ (i : h.J) (W : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ W ≤ h.W i → ∀ f, pbT b (dl W f) (b ⁻¹ᵁ (m ⁻¹ᵁ W)) = pbT a (h.d i _ ((Y.q.left.app W).hom f)) (b ⁻¹ᵁ (m ⁻¹ᵁ W))) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h hdd hB K _ _ φ hΘ Z p m hm
  have := Y.smooth_q
  have hs := (surjective_q Y).1
  choose V hV using fun i => (hB i).1
  choose e he hq using fun i => exists_desc Y (V i) (h.d i) D (hV i ▸ h.lift i)
    fun V' hV' => (hB i).2.2.2 0 V' ((pre_mono _ hV').trans (hV i).ge)
  have hc := fun i i' W hW f => desc_agree Y h hdd φ hΘ p m hm V hV e hq i i' W hW f
  have hcov : ∀ y, ∃ i, m y ∈ V i := fun y => by
    obtain ⟨x, hx⟩ := Y.q.left.surjective (m y)
    have hx' : x ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    rw [hV] at hi
    exact ⟨i, hx ▸ hi⟩
  have hloc : ∀ i, KS.LocDerK p Q.P.A.hom m (fun r => φ (D r)) (V i) (fun W f => (m.app W).hom (e i W f)) := by
    intro i
    refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h' hW f => ?_, fun W hW r => ?_⟩
    · rw [(he i).1.1 W hW, map_add]
    · rw [(he i).1.2.1 W hW, map_add, map_mul, map_mul]
    · rw [(he i).1.2.2 W W' h' hW, rsT_eq (pre_mono m h'), res_app m h']
    · rw [(he i).2 W hW, app_const φ _ p m hm]
  obtain ⟨dl, hdl, hu⟩ := InteriorKS.glue_along p Q.P.A.hom m _ V hcov (fun i W f => (m.app W).hom (e i W f)) hloc hc
  refine ⟨dl, hdl, fun Z' a b w i W hWi f => ?_⟩
  have hWV : W ≤ V i := fun x hx => by
    obtain ⟨y, rfl⟩ := Y.q.left.surjective x
    exact (hWi.trans (hV i).le) hx
  have e1 : dl W f = (m.app W).hom (e i W f) := by
    refine hu W f _ fun j => ?_
    rw [res_app m inf_le_left, ← (he i).1.2.2 W (W ⊓ V j) inf_le_left hWV f]
    exact hc i j _ (le_inf (inf_le_left.trans hWV) inf_le_right) _
  have hle : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ a ⁻¹ᵁ (Y.q.left ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  rw [e1, pbT, pbT, dif_pos (le_refl _), dif_pos hle, ← hq i W hWV]
  have k : ∀ (c : Z' ⟶ Q.P.A.left) (_ : c = b ≫ m) (hc : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ c ⁻¹ᵁ W) x,
      (b.appLE (m ⁻¹ᵁ W) (b ⁻¹ᵁ (m ⁻¹ᵁ W)) (le_refl _)).hom ((m.app W).hom x) = (c.appLE W _ hc).hom x := by
    rintro _ rfl hc x
    rw [Scheme.Hom.comp_appLE]
    rfl
  rw [k (a ≫ Y.q.left) w (by rw [Scheme.Hom.comp_preimage]; exact hle)]
  exact congrArg (fun ψ => ψ.hom (e i W f)) (Scheme.Hom.comp_appLE a Y.q.left W _ hle)

end GlobalTheory.Heat.AbConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocTuplesThetaOfAdm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.Poinc.exists_locTuples_theta_of_adm : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), S.Big → SharpOver F W ρ.P u → (∀ w, (spMap S.R.val.toRingHom ≫ u) w ∈ genericPoints F.X) → ∃ (ι : ℕ) (K : Type) (_ : Fintype K) (Jk : K → Type) (_ : ∀ k, Fintype (Jk k)) (t : ∀ k, Jk k → Ω), 1 ≤ ι ∧ (∀ k j, t k j ≠ 0) ∧ ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, ∃ k, ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ FinalForm.u₀ u T ξ → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ (∀ j, OrdGe M T ξ (t k j) a) ∧ ∃ j, OrdEq M T ξ (t k j) a := by
  intro g n hg hn hodd F φ hφ W hW o' Ω _ _ _ _ S ρ u hBig hSharp hgen
  have hNodd : Odd S.N := by rw [ρ.N_eq]; exact (ρ.n_odd.pow).pow
  have hN2 := S.N_ge
  have hN3 : 3 ≤ S.N := by obtain ⟨j, hj⟩ := hNodd; omega
  haveI hN0 : NeZero S.N := ⟨by omega⟩
  have hn2 : ρ.n ≠ 2 := by
    intro h2; have := ρ.n_odd; rw [h2] at this; exact (Nat.not_odd_iff_even.2 even_two) this
  have hε : ∃ ε : Fin 8 → ℤ, Nat.Coprime S.N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs) := by
    rw [ρ.N_eq]; exact GlobalTheory.T.exists_e8Form_value_coprime_oddPrimePow W hW ρ.n ρ.k ρ.n_prime hn2
  have hC := GlobalTheory.T.minimiser_cell_function_min_finitely_many_combinations g φ hφ W hW.1 S.N hN3 hε
  choose ιf 𝓛f hιf using fun R : Fin (g + 1) => hC R.1 (Nat.lt_succ_iff.1 R.2)
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by omega)⟩
  haveI : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  haveI : Finite (AddSubgroup S.Gam) :=
    Finite.of_injective (fun H : AddSubgroup S.Gam => (H : Set S.Gam)) SetLike.coe_injective
  haveI : ∀ T₀ : AddSubgroup S.Gam, Finite (T₀ →+ ZMod S.N) := fun T₀ =>
    Finite.of_injective (fun f : T₀ →+ ZMod S.N => (f : T₀ → ZMod S.N)) DFunLike.coe_injective
  let Dt := Σ T₀ : AddSubgroup S.Gam, (T₀ →+ ZMod S.N) × (S.J × (T₀ → ZMod ((S.r * S.N) ^ 2))) × S.Gam
  haveI : Finite Dt := inferInstance
  let Es : Set Ω := {v | v ≠ 0} ∩ Set.range (fun d : Dt => S.FF d.1 d.2.1 d.2.2.1 / S.th d.2.2.2)
  have hEs : Es.Finite := (Set.finite_range _).inter_of_right _
  letI : Fintype Es := hEs.fintype
  let mult : Fin (g + 1) → ℕ := fun R => ∏ s ∈ Finset.univ.erase R, ιf s
  let K := Σ R : Fin (g + 1), Σ _ : {L // L ∈ 𝓛f R}, ((Fin 8 → Fin R.1 → ZMod S.N) → Es)
  let Jk : K → Type := fun k => {ν // ν ∈ k.2.1.1}
  let t : ∀ k, Jk k → Ω := fun k j => ∏ c, ((k.2.2 c : Es) : Ω) ^ ((mult k.1 : ℤ) * j.1 c)
  refine ⟨∏ R, ιf R, K, inferInstance, Jk, fun k => inferInstance, t, ?_, ?_, ?_⟩
  · exact Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.2 fun R _ => by have := (hιf R).1; omega)
  · intro k j
    exact Finset.prod_ne_zero_iff.2 fun c _ => zpow_ne_zero _ (k.2.2 c).2.1
  intro M U₀ EE FinalForm hAdm hEE x
  obtain ⟨r, b₀, μ, e, hr, hsym, hpos, hμ, hmin, he, htr⟩ :=
    GlobalTheory.T.thetaModel_local_lattice_fourierParts_orders g n hg hn hodd F W hW o' Ω S ρ u hBig hSharp hgen hN0 M U₀ EE FinalForm hAdm hEE x
  let R : Fin (g + 1) := ⟨r, by omega⟩
  obtain ⟨hιR, hL⟩ := hιf R
  obtain ⟨L, hLmem, hLprop⟩ := hL b₀ hsym hpos μ hμ hmin
  have heE : ∀ c, e c ∈ Es := fun c => by
    obtain ⟨hne, T₀, c', κ, x₀, _, hc⟩ := he c
    exact ⟨hne, ⟨⟨T₀, c', κ, x₀⟩, hc.symm⟩⟩
  refine ⟨⟨R, ⟨L, hLmem⟩, fun c => ⟨e c, heE c⟩⟩, ?_⟩
  intro T ξ hthr hspec
  obtain ⟨π, hπs, hπmin, hq⟩ := htr T ξ hthr hspec

  set b' := T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap with hb'
  have hb'sym : ∀ x y, b' x y = b' y x := fun x y => T.symm _ _
  have hb'psd : ∀ x, 0 ≤ b' x x := GlobalTheory.T.bilinForm_psd_of_minimal_tuple_modN (N := S.N) (by omega) W hW b' (μ 0) fun α hα =>
    hπmin 0 α fun u i => by obtain ⟨m, hm⟩ := hα u i; simp [hm, hμ]
  obtain ⟨hle, ν₀, hν₀, heq⟩ := hLprop b' hb'sym hb'psd hπmin
  have hφeq : φ.evalZ b' = φ.evalZ T.β := by
    have hpull : pull π.toIntLinearMap T.β = b' := LinearMap.ext₂ fun _ _ => rfl
    rw [← hpull]; exact evalZ_pull φ (r := π.toIntLinearMap) hπs T.β
  have hφ0 : 0 ≤ φ.evalZ b' :=
    (hφ (Fin r → ℤ) (by rw [Module.finrank_fin_fun]; exact hr)).evalZ_nonneg (mem_balForms_int.2 hb'sym) hb'psd

  set y : Sp (FractionRing T.V) ⟶ M.Z := jK T.V ≫ ξ with hy
  set z₀ := y (IsLocalRing.closedPoint (FractionRing T.V)) with hz₀
  have hsp : ∀ w, y w ⤳ z₀ := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton y _)
  have hz₀U : z₀ ∈ U₀ := by
    obtain ⟨ξ₀, hξ₀, -⟩ := hthr
    rw [hz₀, hy, ← hξ₀]
    have hm : (ξ₀ ≫ U₀.ι) (IsLocalRing.closedPoint (FractionRing T.V)) ∈ Set.range U₀.ι := by
      exact ⟨ξ₀ (IsLocalRing.closedPoint (FractionRing T.V)), rfl⟩
    rw [U₀.range_ι] at hm; exact hm
  have hO : M.ringOn U₀ ≤ M.O z₀ := RatModel.ringOn_le_O (M := M) hz₀U
  have hOv := hAdm.1
  have hFFR : ∀ (T₀ : AddSubgroup S.Gam) c' κ, S.FF T₀ c' κ ∈ S.R := by
    intro T₀ c' κ
    haveI : Fintype T₀ := Fintype.ofFinite _
    unfold ThetaSys.FF
    rw [finsum_eq_sum_of_fintype]
    exact Subalgebra.sum_mem _ fun t _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (S.ev_mem _ _))
  have hunit : ∀ c, e c ≠ 0 ∧ e c ∈ M.O z₀ ∧ (e c)⁻¹ ∈ M.O z₀ := by
    intro c
    obtain ⟨hne, T₀, c', κ, x₀, hiso, hc⟩ := he c
    rw [hc] at hne ⊢
    have hF : S.FF T₀ c' κ ≠ 0 := (div_ne_zero_iff.1 hne).1
    have hth : S.th x₀ ≠ 0 := (div_ne_zero_iff.1 hne).2
    refine ⟨hne, hO ?_, hO ?_⟩
    · rw [div_eq_mul_inv]; exact Subalgebra.mul_mem _ (hOv.le (hFFR T₀ c' κ)) (hOv.th_unit x₀ hth)
    · rw [inv_div, div_eq_mul_inv]
      exact Subalgebra.mul_mem _ (hOv.le (S.th_mem x₀)) (hOv.FF_unit T₀ c' κ hiso hF)
  have hvne : ∀ c, M.val y (e c) ≠ 0 := by
    intro c
    have h1 := RatModel.val_mul (M := M) hsp (hunit c).2.1 (hunit c).2.2
    rw [mul_inv_cancel₀ (hunit c).1, RatModel.val_one] at h1
    exact left_ne_zero_of_mul_eq_one h1.symm
  have hpow : ∀ c, M.val y (e c ^ S.N) = M.val y (e c) ^ S.N := by
    intro c
    have := GlobalTheory.T.integralModel_value_prod_zpow_localUnits M y z₀ hsp (Finset.univ : Finset Unit) (fun _ => e c) (fun _ => (S.N : ℤ)) fun _ => hunit c
    simpa using this
  choose v w hvw using fun c => GlobalTheory.T.fractionRing_eq_uniformiser_zpow_mul_unit T.irr (M.val y (e c)) (hvne c)

  have hϖ0 : algebraMap T.V (FractionRing T.V) T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T.V (FractionRing T.V))).2 T.irr.ne_zero
  have hunitK : ∀ (a : T.Vˣ) (k : ℤ), algebraMap T.V (FractionRing T.V) ((a ^ k : T.Vˣ) : T.V) =
      (algebraMap T.V (FractionRing T.V) (a : T.V)) ^ k := by
    intro a k
    have h1 : algebraMap T.V (FractionRing T.V) ((a ^ k : T.Vˣ) : T.V) =
        ((Units.map (algebraMap T.V (FractionRing T.V)).toMonoidHom (a ^ k) : (FractionRing T.V)ˣ) : FractionRing T.V) := rfl
    rw [h1, map_zpow, Units.val_zpow_eq_zpow_val]; rfl
  have hNv : ∀ c, (S.N : ℤ) * v c = qW W b' (μ c) := by
    intro c
    obtain ⟨hq0, w', hw'⟩ := hq c
    rw [hpow] at hw'
    have h2 : algebraMap T.V (FractionRing T.V) T.ϖ ^ ((S.N : ℤ) * v c) *
        algebraMap T.V (FractionRing T.V) ((w c ^ (S.N : ℤ) : T.Vˣ) : T.V) =
        algebraMap T.V (FractionRing T.V) T.ϖ ^ (((qW W b' (μ c)).toNat : ℕ) : ℤ) *
        algebraMap T.V (FractionRing T.V) (w' : T.V) := by
      rw [hunitK, mul_comm (S.N : ℤ) (v c), zpow_mul, zpow_natCast, zpow_natCast, ← mul_pow, ← hvw c, hw',
        map_mul, map_pow, zpow_natCast]
    have := GlobalTheory.T.uniformiser_zpow_mul_unit_exponent_unique T.irr _ _ _ _ h2
    rw [this, Int.toNat_of_nonneg hq0]
  have hmR : (∏ R', ιf R') = ιf R * mult R := (Finset.mul_prod_erase Finset.univ ιf (Finset.mem_univ R)).symm
  let E : ((Fin 8 → Fin r → ZMod S.N) → ℤ) → ℤ := fun ν => ∑ c, v c * ((mult R : ℤ) * ν c)
  have hE : ∀ ν, (S.N : ℝ) * (E ν : ℝ) = (mult R : ℝ) * ∑ c, (ν c : ℝ) * (qW W b' (μ c) : ℝ) := by
    intro ν
    simp only [E, Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← hNv c]; push_cast; ring
  have hzs : ∀ (f : (Fin 8 → Fin r → ZMod S.N) → ℤ) (s : Finset (Fin 8 → Fin r → ZMod S.N)),
      ∏ c ∈ s, algebraMap T.V (FractionRing T.V) T.ϖ ^ f c = algebraMap T.V (FractionRing T.V) T.ϖ ^ ∑ c ∈ s, f c := by
    intro f s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hϖ0]
  have hval : ∀ ν, M.val y (∏ c, e c ^ ((mult R : ℤ) * ν c)) = algebraMap T.V (FractionRing T.V) T.ϖ ^ E ν *
      algebraMap T.V (FractionRing T.V) ((∏ c, w c ^ ((mult R : ℤ) * ν c) : T.Vˣ) : T.V) := by
    intro ν
    rw [GlobalTheory.T.integralModel_value_prod_zpow_localUnits M y z₀ hsp _ _ _ fun c => hunit c]
    simp only [hvw, mul_zpow, Finset.prod_mul_distrib, ← zpow_mul, ← hunitK]
    rw [hzs, Units.coe_prod, map_prod]
  have hprodO : ∀ ν : (Fin 8 → Fin r → ZMod S.N) → ℤ, (∏ c, e c ^ ((mult R : ℤ) * ν c)) ∈ M.O z₀ := by
    intro ν
    refine Subalgebra.prod_mem _ fun c _ => ?_
    rcases Int.eq_nat_or_neg ((mult R : ℤ) * ν c) with ⟨k, hk | hk⟩ <;> rw [hk]
    · rw [zpow_natCast]; exact Subalgebra.pow_mem _ (hunit c).2.1 k
    · rw [zpow_neg, zpow_natCast, ← inv_pow]; exact Subalgebra.pow_mem _ (hunit c).2.2 k
  have hιeq : ((∏ R', ιf R' : ℕ) : ℝ) = (ιf R : ℝ) * mult R := by rw [hmR]; push_cast; ring
  have hNpos : (0 : ℝ) < S.N := by exact_mod_cast (show 0 < S.N by omega)
  have hge : ∀ ν ∈ L, ((∏ R', ιf R' : ℕ) : ℝ) * φ.evalZ T.β ≤ E ν := by
    intro ν hν
    have h1 := mul_le_mul_of_nonneg_left (hle ν hν) (Nat.cast_nonneg (α := ℝ) (mult R))
    rw [← hE ν] at h1
    rw [hιeq, ← hφeq]
    refine le_of_mul_le_mul_left ?_ hNpos
    nlinarith
  have hE0 : ((E ν₀ : ℤ) : ℝ) = ((∏ R', ιf R' : ℕ) : ℝ) * φ.evalZ T.β := by
    have h1 := congrArg (HMul.hMul (mult R : ℝ)) heq
    rw [← hE ν₀] at h1
    rw [hιeq, ← hφeq]
    refine mul_left_cancel₀ hNpos.ne' ?_
    nlinarith
  have hEnn : 0 ≤ E ν₀ := by
    have : (0 : ℝ) ≤ (E ν₀ : ℝ) := by
      rw [hE0]; exact mul_nonneg (Nat.cast_nonneg _) (hφeq ▸ hφ0)
    exact_mod_cast this
  refine ⟨(E ν₀).toNat, ?_, ?_, ?_⟩
  · rw [← hE0]; exact_mod_cast Int.toNat_of_nonneg hEnn
  · intro j
    show GlobalTheory.Poinc.OrdGe M T ξ (∏ c, e c ^ ((mult R : ℤ) * j.1 c)) _
    have hle' : E ν₀ ≤ E j.1 := by
      have := hge j.1 j.2; rw [← hE0] at this; exact_mod_cast this
    obtain ⟨d, hd⟩ : ∃ d : ℕ, E j.1 = ((E ν₀).toNat : ℤ) + d := ⟨(E j.1 - E ν₀).toNat, by omega⟩
    refine ⟨hprodO j.1, T.ϖ ^ d * ((∏ c, w c ^ ((mult R : ℤ) * j.1 c) : T.Vˣ) : T.V), ?_⟩
    rw [hval, hd, map_mul, map_mul, map_pow, map_pow, zpow_add₀ hϖ0, zpow_natCast, zpow_natCast, mul_assoc]
  · refine ⟨⟨ν₀, hν₀⟩, ?_⟩
    show GlobalTheory.Poinc.OrdEq M T ξ (∏ c, e c ^ ((mult R : ℤ) * ν₀ c)) _
    refine ⟨∏ c, w c ^ ((mult R : ℤ) * ν₀ c), ?_⟩
    rw [hval, map_mul, map_pow, ← zpow_natCast, Int.toNat_of_nonneg hEnn]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExportFromReciprocityTheoremsStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.export_from_reciprocity_theorems : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.SerStd.SeriesRatS → ExportSt := by
  first | exact @GlobalTheory.BigOn.exportSt_of_reading | exact GlobalTheory.BigOn.exportSt_of_reading | (intros; apply GlobalTheory.BigOn.exportSt_of_reading <;> assumption)
end

