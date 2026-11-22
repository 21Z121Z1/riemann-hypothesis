import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfHasRepUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2487
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2401
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointDisjointUnionRepresentingAdditiveFami
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.ProdGlue

theorem opens_disjoint_of {Y : Scheme.{0}} {U U' : Y.Opens} (h : ∀ z, z ∈ U → z ∉ U') : Disjoint U U' :=
  disjoint_iff.2 (eq_bot_iff.2 fun z hz ↦ (h z hz.1 hz.2).elim)

theorem not_mem_of_disjoint {Y : Scheme.{0}} {U U' : Y.Opens} (h : Disjoint U U') {z : Y} (hz : z ∈ U)
    (hz' : z ∈ U') : False := by
  have := h.le_bot (show z ∈ U ⊓ U' from ⟨hz, hz'⟩)
  simpa using this

theorem rep_exists {S : Scheme.{0}} (A : Over S) [GrpObj A] {κ : Type} [Finite κ] (X : Over S)
    (V : κ → X.left.Opens) (hV : ⨆ i, V i = ⊤) (hVd : Pairwise fun i i' => Disjoint (V i) (V i'))
    (Bt : Over S) (B : κ → Over S) (j : ∀ i, B i ⟶ Bt) [∀ i, IsOpenImmersion (j i).left]
    (hj : ⨆ i, (j i).left.opensRange = ⊤)
    (hjd : Pairwise fun i i' => Disjoint (j i).left.opensRange (j i').left.opensRange)
    (b : ∀ i, B i ⟶ Over.mk ((V i).ι ≫ X.hom)) (bt : Bt ⟶ X) (hb : ∀ i, j i ≫ bt = b i ≫ Over.homMk (V i).ι)
    (P : ∀ i, LB (A ⊗ B i).left) (Pt : LB (A ⊗ Bt).left) (hP : ∀ i, Rep A (b i) (P i)) (hPt : Pt.IsLB)
    (hiso : ∀ i, LBIso (Pt.pull (A ◁ j i).left) (P i)) (T : Over S) (t : T ⟶ X) (N : LB (A ⊗ T).left)
    (hN : Fam A N) : ∃ x : T ⟶ Bt, x ≫ bt = t ∧ LBIso N (ev Pt (fst A T) (snd A T ≫ x)) := by
  let W : κ → T.left.Opens := fun i ↦ t.left ⁻¹ᵁ V i
  let Ti : κ → Over S := fun i ↦ Over.mk ((W i).ι ≫ T.hom)
  let w : ∀ i, Ti i ⟶ T := fun i ↦ Over.homMk (W i).ι
  let ti : ∀ i, Ti i ⟶ Over.mk ((V i).ι ≫ X.hom) := fun i ↦ Over.homMk (t.left ∣_ V i) (by
    simp [Ti, W, morphismRestrict_ι_assoc])
  have hti : ∀ i, ti i ≫ Over.homMk (V i).ι = w i ≫ t := fun i ↦ by
    ext1; simp [ti, w, W, morphismRestrict_ι]
  have hNi : ∀ i, Fam A (ev N (fst A (Ti i)) (snd A (Ti i) ≫ w i)) := fun i ↦ Model.fam_ev hN (w i)
  choose x hx _ using fun i ↦ (hP i).univ (Ti i) (ti i) _ (hNi i)
  have hWc : ⨆ i, (W i).ι.opensRange = ⊤ := by
    refine eq_top_iff.2 fun z _ ↦ ?_
    have : t.left z ∈ ⨆ i, V i := hV ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by simpa [W] using hi⟩
  have hWd : _root_.Pairwise fun i i' ↦ Disjoint (W i).ι.opensRange (W i').ι.opensRange := by
    intro i i' h
    refine opens_disjoint_of fun z hz hz' ↦ ?_
    simp only [Scheme.Opens.opensRange_ι, W] at hz hz'
    exact not_mem_of_disjoint (hVd h) hz hz'
  obtain ⟨hT⟩ := nonempty_isColimit_cofanMk_of (fun i ↦ (W i).ι) hWc hWd
  let xl : T.left ⟶ Bt.left := Cofan.IsColimit.desc hT fun i ↦ (x i).left ≫ (j i).left
  have hxl : ∀ i, (W i).ι ≫ xl = (x i).left ≫ (j i).left := fun i ↦ Cofan.IsColimit.fac hT _ i
  have hxo : xl ≫ Bt.hom = T.hom := Cofan.IsColimit.hom_ext hT _ _ fun i ↦ by
    change (W i).ι ≫ _ = (W i).ι ≫ _
    rw [reassoc_of% hxl i, Over.w (j i), Over.w (x i)]
    rfl
  let xx : T ⟶ Bt := Over.homMk xl hxo
  have wxx : ∀ i, w i ≫ xx = x i ≫ j i := fun i ↦ by
    ext1
    simp only [Over.comp_left, Over.homMk_left, w, xx]
    exact hxl i
  have hxt : xx ≫ bt = t := by
    ext1
    refine Cofan.IsColimit.hom_ext hT _ _ fun i ↦ ?_
    change (W i).ι ≫ _ = (W i).ι ≫ _
    have e : w i ≫ xx ≫ bt = w i ≫ t := by
      rw [reassoc_of% wxx i, hb i, reassoc_of% (hx i).1, hti i]
    simpa [w, xx] using congrArg (fun q ↦ q.left) e
  refine ⟨xx, hxt, ?_⟩
  have hNl := hN.isLB
  refine (same_id_iff hNl hPt xx).1 ((same_iff hNl hPt _ _).2 ?_)
  have hwo : ∀ i, IsOpenImmersion (w i).left := fun i ↦ by
    show IsOpenImmersion (W i).ι; infer_instance
  have hwa : ∀ i, IsOpenImmersion (A ◁ w i).left := fun i ↦
    (@isOpenImmersion_whiskerLeft_left_and_range _ A _ _ (w i) (hwo i)).1
  have hwr : ∀ i z, z ∈ (A ◁ w i).left.opensRange ↔ (snd A T).left z ∈ W i := fun i z ↦ by
    have := (@isOpenImmersion_whiskerLeft_left_and_range _ A _ _ (w i) (hwo i)).2
    change z ∈ Set.range (A ◁ w i).left ↔ _
    rw [this, Set.mem_preimage]
    change _ ∈ Set.range (W i).ι ↔ _
    rw [Scheme.Opens.range_ι]
    rfl
  rw [← sub_eq_zero]
  refine GlobalTheory.T.cechPicard_eq_zero_of_trivial_on_disjoint_cover (fun i ↦ (A ◁ w i).left) ?_ ?_ _ fun i ↦ ?_
  · refine eq_top_iff.2 fun z _ ↦ ?_
    have : t.left ((snd A T).left z) ∈ ⨆ i, V i := hV ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hwr i z).2 hi⟩
  · intro i i' h
    refine opens_disjoint_of fun z hz hz' ↦ ?_
    exact not_mem_of_disjoint (hVd h) ((hwr i z).1 hz) ((hwr i' z).1 hz')
  · rw [map_sub, pull_evc, pull_evc, sub_eq_zero]
    simp only [whiskerLeft_fst, whiskerLeft_snd_assoc, whiskerLeft_snd, Category.comp_id]
    rw [wxx i, ← Category.assoc, evc_comp_of_iso (j i) hPt (hP i).fam.isLB (hiso i)]
    exact (cls_eq_iff (hNi i).isLB (pull_isLB (hP i).fam.isLB _)).2 (hx i).2

end GlobalTheory.DualCon.ProdGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointwiseCochainCoboundaryEqChernCocycleAl
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem commAlgFunctorCoboundaryOne_apply_of_eq_sub_vanishing {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}
    {m : C1 F} {z z' : C2 F} (h : d1 F m = z - z') {T T' T'' : C} (a : T ⟶ T') (b : T' ⟶ T'')
    (h0 : z' T T' T'' a b = 0) :
    mp F b (m T T' a) - m T T'' (a ≫ b) + m T' T'' b = z T T' T'' a b := by
  rw [← d1_apply, h]
  simp only [Pi.sub_apply, h0, sub_zero]

theorem exists_crystallineCochain_coboundary_eq_chernCocycle {R : Type} [CommRing R] {I : Ideal R} {g : DividedPowers I} {X : Scheme.{0}}
    {s : X ⟶ Sp R} {L : LB X} {w : Z2 (O g s)} (hw : IsChern g s L (CatCoh.H2.mk _ w)) :
    ∃ V : C1 (O g s), ∀ (T T' T'' : Thick g s) (a : T ⟶ T') (b : T' ⟶ T''), IsSmall g s L.U T → T''.J = ⊥ →
      d1 _ V T T' T'' a b = w.1 T T' T'' a b := by
  obtain ⟨i, hi, u, ℓ, hu, hℓ, hz⟩ := hw
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hz
  obtain ⟨m, hm⟩ := hz
  classical
  have sm : ∀ {T T' : Thick g s} (_ : T ⟶ T'), IsSmall g s L.U T → IsSmall g s L.U T' := by
    rintro T T' a ⟨j, hj⟩
    exact ⟨j, a.le_preimage hj⟩
  refine ⟨fun T T' a ↦ if h : IsSmall g s L.U T then m ⟨T, h⟩ ⟨T', sm a h⟩ (ObjectProperty.homMk a) else 0, ?_⟩
  intro T T' T'' a b h hJ
  have h1 := sm a h
  have h2 := sm b h1
  rw [d1_apply]
  simp only [dif_pos h, dif_pos h1]
  refine commAlgFunctorCoboundaryOne_apply_of_eq_sub_vanishing hm (T := ⟨T, h⟩) (T' := ⟨T', h1⟩) (T'' := ⟨T'', h2⟩) (ObjectProperty.homMk a)
    (ObjectProperty.homMk b) ?_
  have := (hℓ ⟨T, h⟩ ⟨T', h1⟩ ⟨T'', h2⟩ (ObjectProperty.homMk a) (ObjectProperty.homMk b)).1
  exact Ideal.mem_bot.1 (hJ.le this)

theorem exists_pt_d_eq_chern {R : Type} [CommRing R] {X : Over (Sp R)} {L : LB X.left}
    {w : Z2 (O (dp0 R) (X.hom ≫ 𝟙 _))} (hw : IsChern (dp0 R) _ L (CatCoh.H2.mk _ w)) :
    ∃ V : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (z : Pt X E) (z' : Pt X E'),
      (trivAt z ⟶ trivAt z') → E',
      ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E'']
        [Algebra R E''] (z : Pt X E) (z' : Pt X E') (z'' : Pt X E'') (a : trivAt z ⟶ trivAt z')
        (b : trivAt z' ⟶ trivAt z'') (ψ : E' →ₐ[R] E''), b.φ = ψ → Sm L.U z →
        ψ (V E E' z z' a) - V E E'' z z'' (a ≫ b) + V E' E'' z' z'' b = w.1 _ _ _ a b := by
  obtain ⟨V, hV⟩ := exists_crystallineCochain_coboundary_eq_chernCocycle hw
  refine ⟨fun E _ _ E' _ _ z z' a ↦ V _ _ a, ?_⟩
  intro E _ _ E' _ _ E'' _ _ z z' z'' a b ψ hb hz
  subst hb
  exact hV _ _ _ a b hz rfl

theorem exists_pointwiseCochain_coboundary_eq_chernCocycle : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (L : LB X.left) (w : Z2 (O (dp0 R) (X.hom ≫ 𝟙 _))), IsChern (dp0 R) _ L (CatCoh.H2.mk _ w) → ∃ n : Fn1 X, ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E''] [Algebra R E''] (φ : E →ₐ[R] E') (ψ : E' →ₐ[R] E'') (z : Pt X E), Sm L.U z → ψ (n E E' φ z) - n E E'' (ψ.comp φ) z + n E' E'' ψ (spOver φ ≫ z) = w.1 _ _ _ (trivMap φ z) (trivMap ψ (spOver φ ≫ z)) := by
  intro R _ X L w hw
  obtain ⟨V, hV⟩ := exists_pt_d_eq_chern hw
  refine ⟨fun E _ _ E' _ _ φ z ↦ V E E' z _ (trivMap φ z), ?_⟩
  intro E _ _ E' _ _ E'' _ _ φ ψ z hz
  have gen : ∀ (y : Pt X E'') (_ : y = spOver (ψ.comp φ) ≫ z) (f : trivAt z ⟶ trivAt y),
      (∀ c, f.φ c = ψ (φ c)) → V E E'' z _ (trivMap (ψ.comp φ) z) = V E E'' z y f := by
    intro y hy f hf
    subst hy
    exact congrArg (V E E'' z _) (Thick.hom_ext fun c ↦ (hf c).symm)
  have hc := gen (spOver ψ ≫ spOver φ ≫ z) (by rw [← Category.assoc, spOver_comp])
    (trivMap φ z ≫ trivMap ψ (spOver φ ≫ z)) fun _ ↦ rfl
  have key := hV E E' E'' z _ _ (trivMap φ z) (trivMap ψ (spOver φ ≫ z)) ψ rfl hz
  rw [← hc] at key
  exact key

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointwiseGeneratorOfDualNumberLineBundleGe
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

theorem epsGen_epsEv_apply {E : Type} [CommRing E] [Algebra R E] (e : Pt (epsR R) E) (u : DualNumber E) :
    epsEv e u = u.fst + u.snd * ptAlg (D := DualNumber R) e DualNumber.eps := by
  simp [epsEv, DualNumber.lift_apply_apply]

theorem epsGen_epsEv_nat {E E' : Type} [CommRing E] [Algebra R E] [CommRing E'] [Algebra R E']
    (ψ : E →ₐ[R] E') (e : Pt (epsR R) E) (u : DualNumber E) :
    epsEv (spOver ψ ≫ e) (epsHom ψ u) = ψ (epsEv e u) := by
  obtain ⟨h1, h2, -⟩ := dualNumberAlgHomMap_fst_snd_logDerivative R E E' ψ u
  rw [epsGen_epsEv_apply, epsGen_epsEv_apply, h1, h2, ptAlg_comp, map_add, map_mul]
  rfl

theorem epsGen_spMap_eq {E : Type} [CommRing E] [Algebra R E] (e : Pt (epsR R) E) (p : Sp E) :
    (spMap (epsEv e : DualNumber E →+* E)).base p = (spMap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E)).base p := by
  apply PrimeSpectrum.ext
  ext u
  change u ∈ (PrimeSpectrum.comap (epsEv e : DualNumber E →+* E) p).asIdeal ↔
    u ∈ (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E) p).asIdeal
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  have hc : ptAlg (D := DualNumber R) e DualNumber.eps ∈ p.asIdeal :=
    p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, ← map_mul, DualNumber.eps_mul_eps, map_zero]; exact p.asIdeal.zero_mem)
  change epsEv e u ∈ p.asIdeal ↔ u.fst ∈ p.asIdeal
  rw [epsGen_epsEv_apply]
  constructor
  · intro h
    have := p.asIdeal.sub_mem h (p.asIdeal.mul_mem_left u.snd hc)
    simpa using this
  · intro h
    exact p.asIdeal.add_mem h (p.asIdeal.mul_mem_left u.snd hc)

theorem epsGen_mem {E : Type} [CommRing E] [Algebra R E] (e : Pt (epsR R) E) {Y : Scheme.{0}}
    (y : Sp (DualNumber E) ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ (spMap (epsEv e : DualNumber E →+* E) ≫ y) ⁻¹ᵁ U) :
    ⊤ ≤ (spMap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E) ≫ y) ⁻¹ᵁ U := by
  intro p _
  have := h (Set.mem_univ p)
  change y.base ((spMap (epsEv e : DualNumber E →+* E)).base p) ∈ U at this
  change y.base ((spMap (TrivSqZeroExt.fstHom R E E : DualNumber E →+* E)).base p) ∈ U
  rwa [← epsGen_spMap_eq e p]

variable {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem epsGen_red_ptV {v : epsR R ⟶ B} (hv : IsTangent v) {E : Type} [CommRing E] [Algebra R E] (x : Pt A E) :
    spOver (TrivSqZeroExt.fstHom R E E) ≫ ptV v x = x ≫ AbDual.inl A B := by
  have hv' : spOver (TrivSqZeroExt.fstHom R R R) ≫ v = toUnit _ ≫ η[B] := by
    refine Over.OverMorphism.ext ?_
    refine hv.trans ?_
    simp [spMap]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [ptV, Category.assoc, lift_fst, Category.comp_id]
    rw [← Category.assoc, spOver_comp]
    have : (TrivSqZeroExt.fstHom R E E).comp (TrivSqZeroExt.inlAlgHom R E E) = AlgHom.id R E := by ext; simp
    rw [this]
    refine Over.OverMorphism.ext ?_
    simp [spOver, spMap]
  · simp only [ptV, Category.assoc, lift_snd]
    rw [← Category.assoc, spOver_comp]
    have : (TrivSqZeroExt.fstHom R E E).comp (EpsWeil.epsMap R E) =
        (Algebra.ofId R E).comp (TrivSqZeroExt.fstHom R R R) := by
      apply DualNumber.algHom_ext
      simp [EpsWeil.epsMap]
    rw [this, ← spOver_comp, Category.assoc, hv', Hom.one_def, ← Category.assoc, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _

theorem epsGen_key (v : epsR R ⟶ B) {E : Type} [CommRing E] [Algebra R E] (z : Pt (A ⊗ epsR R) E) :
    z ≫ lift (fst A (epsR R)) (snd A (epsR R) ≫ v) =
      spOver (epsEv (z ≫ snd _ _)) ≫ ptV v (z ≫ fst _ _) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [ptV, Category.assoc, lift_fst]
    rw [← Category.assoc (spOver _), spOver_comp]
    have : (epsEv (z ≫ snd _ _)).comp (TrivSqZeroExt.inlAlgHom R E E) = AlgHom.id R E := by
      ext a; simp [epsEv, DualNumber.lift_apply_inl]
    rw [this, spOver_id, Category.id_comp]
  · simp only [ptV, Category.assoc, lift_snd]
    rw [← Category.assoc (spOver _), spOver_comp]
    have : (epsEv (z ≫ snd _ _)).comp (EpsWeil.epsMap R E) = ptAlg (z ≫ snd _ _) := by
      apply DualNumber.algHom_ext
      simp [EpsWeil.epsMap, epsEv]
    rw [this, spOver_ptAlg, Category.assoc]

theorem exists_isPtGen_of_isEpsGen : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left), P.IsLB → ∀ v : epsR R ⟶ B, IsTangent v → ∀ T, IsEpsGen P v T →
    ∃ t, IsPtGen P (lift (fst A (epsR R)) (snd A (epsR R) ≫ v)) t := by
  intro R _ A B _ _ P _ v hv T hT
  obtain ⟨T1, T2, T3⟩ := hT
  have memV : ∀ (E : Type) [CommRing E] [Algebra R E] (x : Pt A E) (i : P.ι), ⊤ ≤ x.left ⁻¹ᵁ chartsA P i →
      ⊤ ≤ (ptV v x).left ⁻¹ᵁ P.U i := by
    intro E _ _ x i h
    apply (evU_dl_rules.2.2.2.2.2) _ E (ptV v x).left (P.U i)
    have h1 : ⊤ ≤ (x ≫ AbDual.inl A B).left ⁻¹ᵁ P.U i := h
    rw [← epsGen_red_ptV hv x] at h1
    exact h1
  have memA : ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt (A ⊗ epsR R) E) (i : P.ι),
      ⊤ ≤ (z ≫ CartesianMonoidalCategory.lift (fst A (epsR R)) (snd A (epsR R) ≫ v)).left ⁻¹ᵁ P.U i →
      ⊤ ≤ (z ≫ fst _ _).left ⁻¹ᵁ chartsA P i := by
    intro E _ _ z i h
    rw [epsGen_key v z, Over.comp_left, spOver_left] at h
    have h2 := epsGen_mem (z ≫ snd _ _) _ _ h
    have h3 : ⊤ ≤ (spOver (TrivSqZeroExt.fstHom R E E) ≫ ptV v (z ≫ fst _ _)).left ⁻¹ᵁ P.U i := h2
    rw [epsGen_red_ptV hv] at h3
    exact h3
  refine ⟨fun E _ _ z i ↦ epsEv (z ≫ snd _ _) (T E (z ≫ fst _ _) i), ⟨?_, ?_, ?_⟩⟩
  · intro E _ _ z i h
    exact (T1 E (z ≫ fst _ _) i (memA E z i h)).map _
  · intro E _ _ E' _ _ ψ z i h
    have h' := memA E z i h
    simp only [Category.assoc]
    rw [T2 E E' ψ (z ≫ fst _ _) i h', epsGen_epsEv_nat]
  · intro E _ _ z i j hi hj
    have hi' := memA E z i hi
    have hj' := memA E z j hj
    have hij : ⊤ ≤ (ptV v (z ≫ fst _ _)).left ⁻¹ᵁ (P.U i ⊓ P.U j) :=
      fun p hp ↦ ⟨memV E _ i hi' hp, memV E _ j hj' hp⟩
    simp only
    rw [T3 E (z ≫ fst _ _) i j hi' hj', map_mul, epsGen_key v z, Over.comp_left, spOver_left,
      (evU_dl_rules.1) _ _ E (epsEv (z ≫ snd _ _) : DualNumber E →+* E) _ _ _ hij]
    rfl

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarisedAbelianGenericFibreTraitUniformis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitGeneric

theorem exists_polAV_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → UnifTrait D G P.L.L →
    ∃ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom ∧
      LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) := by
  intro R _ _ _ _ D G _ _ P _ hU
  obtain ⟨W, _, _, _, φ, G', _, _, β, D', A', U', -, hinj, -, hGP, hLβ, -⟩ := hU
  have hnz : nonZeroDivisors R ≤ (nonZeroDivisors W).comap φ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hinj
  let ga : FractionRing R →+* FractionRing W := IsLocalization.map (FractionRing W) φ hnz
  have hga : ga.comp (algebraMap R (FractionRing R)) = (algebraMap W (FractionRing W)).comp φ :=
    IsLocalization.map_comp hnz
  have hsq : jK W ≫ spMap φ = spMap ga ≫ jK R := by
    simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hga]
  let GK := (Over.pullback (jK R)).obj G
  let L : LB GK.left := P.L.L.pull (pullback.fst G.hom (jK R))
  have hL : L.IsLB := pull_isLB P.L.isLB _
  have hS : Out.Sym GK L :=
    GlobalTheory.PolBaseChange.sym_pull (isGrpPullback_pullback G (jK R)) (GlobalTheory.WtPoint.sym_of_cp P)
  have := U'.gen_hom
  set ψ₀ := U'.gen.inv.left ≫ pullback.fst G'.hom (jK W) with hψ₀
  have g₀ : IsGrpPullback A'.A G' (jK W) ψ₀ := by
    have : IsMonHom U'.gen.symm.hom := by show IsMonHom U'.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso U'.gen.symm).comp (isGrpPullback_pullback G' (jK W))).congr
      (Category.id_comp _) rfl
  have g₁ : IsGrpPullback A'.A G (spMap ga ≫ jK R) (ψ₀ ≫ β) := (g₀.comp hGP).congr hsq rfl
  have gb := isGrpPullback_pullback G (jK R)
  have w₁ : (ψ₀ ≫ β) ≫ G.hom = (A'.A.hom ≫ spMap ga) ≫ jK R :=
    g₁.1.w.trans (Category.assoc _ _ _).symm
  obtain ⟨α, e₁, e₂⟩ : ∃ α : A'.A.left ⟶ GK.left, α ≫ pullback.fst G.hom (jK R) = ψ₀ ≫ β ∧
      α ≫ GK.hom = A'.A.hom ≫ spMap ga :=
    ⟨gb.1.lift _ _ w₁, gb.1.lift_fst _ _ _, gb.1.lift_snd _ _ _⟩
  have gα : IsGrpPullback A'.A GK (spMap ga) α := gb.cancel (g₁.congr rfl e₁.symm) e₂
  have hgi : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hext : LBIso (A'.L.pull U'.gen.hom.left) (U'.LG.L.pull (pullback.fst G'.hom (jK W))) := U'.ext
  have h1 : LBIso (A'.L.pull (U'.gen.inv.left ≫ U'.gen.hom.left)) (U'.LG.L.pull ψ₀) :=
    LBIso.chartPull (Geo.Tor.chartPullSame A'.L _ (fun _ => U'.gen.hom.left) _ U'.gen.inv.left fun _ => rfl)
      (Geo.Tor.chartPullSame U'.LG.L _ (fun _ => pullback.fst G'.hom (jK W)) _ U'.gen.inv.left fun _ => rfl) hext
  have l₁ : LBIso A'.L (U'.LG.L.pull ψ₀) :=
    LBIso.chartPull (Geo.Tor.chartPullUnpull A'.L _ hgi)
      (Geo.Tor.chartPullSame U'.LG.L _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h1
  have l₂ : LBIso (U'.LG.L.pull ψ₀) (P.L.L.pull (ψ₀ ≫ β)) := GlobalTheory.Ex.GenericFibre.lbIso_pull hLβ ψ₀ rfl
  have l₃ : LBIso (L.pull α) (P.L.L.pull (ψ₀ ≫ β)) :=
    GlobalTheory.Ex.GenericFibre.lbIso_pull (GlobalTheory.PolBaseChange.lbIso_refl hL) α e₁.symm
  have hw : LBIso A'.L (L.pull α) :=
    LBIso.trans A'.isLB (pull_isLB P.L.isLB _) (pull_isLB hL _)
      (LBIso.trans A'.isLB (pull_isLB U'.LG.isLB _) (pull_isLB P.L.isLB _) l₁ l₂) l₃.symm
  exact GlobalTheory.PolFieldDescent.exists_polAV _ _ ga GK L hL hS A' α gα hw

end GlobalTheory.Mum.TraitGeneric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfKaehlerDEqZeroSmoothAffineOpenStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_eq_of_kaehlerD_eq_zero_smooth_affineOpen : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (X : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp k) [Smooth s] (U : X.affineOpens) (u : GlobalTheory.CechDR.Sec s U.1), KaehlerDifferential.D k (GlobalTheory.CechDR.Sec s U.1) u = 0 → ∃ h : GlobalTheory.CechDR.Sec s U.1, h ^ p = u := by
  first | exact @GlobalTheory.ConjSeq.sec_exists_pow_of_D_eq_zero | exact GlobalTheory.ConjSeq.sec_exists_pow_of_D_eq_zero | (intros; apply GlobalTheory.ConjSeq.sec_exists_pow_of_D_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneBirigidifiedSymmetricNoetherianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_eq_one_birigidifiedSymmetric_noetherian : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (A : Over (Sp B)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∃ M : ℕ, 0 < M ∧ ∀ (T : Over (Sp B)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ M = 1 := by
  first | (exact @GlobalTheory.AbDual.exists_pow_eq_one_of_triv_ev_noeth) | (exact GlobalTheory.AbDual.exists_pow_eq_one_of_triv_ev_noeth) | (intros; apply GlobalTheory.AbDual.exists_pow_eq_one_of_triv_ev_noeth  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqOfLogDerivationExtendEqStatement
section
open GlobalTheory.LogDerProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_smul_eq_of_logDerivation_extend_eq : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ (J : Ideal R) (D₁ D₂ : logSub φ J), res (S := S) f φ J D₁ = res (S := S) f φ J D₂ → ∃ c : Submonoid.powers f, c • D₁ = c • D₂ := by
  first | exact @GlobalTheory.LogDerProj.exists_pow_smul_eq_of_res_eq | exact GlobalTheory.LogDerProj.exists_pow_smul_eq_of_res_eq | (intros; apply GlobalTheory.LogDerProj.exists_pow_smul_eq_of_res_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreUniformisationEvenTorusCompleteNormalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_preUniformisation_even_torus_completeNormal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → EvenOn P → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (D : DegPre R) (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), U.P = P ∧ U.gen = gen := by
  first | exact @GlobalTheory.Mum.exists_preU_even | exact GlobalTheory.Mum.exists_preU_even | (intros; apply GlobalTheory.Mum.exists_preU_even <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeAboveValuationEq
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

noncomputable section

namespace GlobalTheory.CNumAtPrime

theorem cNum_eq_c_vp : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (𝔣 : Ideal (OF E)) (l : ℕ), l.Prime →
    ∃ P : HeightOneSpectrum (𝓞 E), (l : 𝓞 E) ∈ P.asIdeal ∧ ((GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.cNum_vp 𝔣 l P : ℚ) : ℝ) = c_vp 𝔣 l := by
  intro E _ _ _ 𝔣 l hl
  classical
  have hlu : ¬ IsUnit (l : 𝓞 E) := by
    intro h
    have h2 := h.map (Algebra.norm ℤ (S := 𝓞 E))
    rw [show (l : 𝓞 E) = algebraMap ℤ (𝓞 E) (l : ℤ) by simp, Algebra.norm_algebraMap] at h2
    have hn : Module.finrank ℤ (𝓞 E) ≠ 0 := Module.finrank_pos.ne'
    rw [isUnit_pow_iff hn, Int.isUnit_iff] at h2
    have := hl.one_lt
    omega
  obtain ⟨M, hM, hlM⟩ := Ideal.exists_le_maximal _ ((Ideal.span_singleton_ne_top hlu))
  have hlP : (l : 𝓞 E) ∈ M := hlM (Ideal.mem_span_singleton_self _)
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    exact Nat.cast_ne_zero.2 hl.ne_zero ((Submodule.mem_bot _).1 hlP)
  let P : HeightOneSpectrum (𝓞 E) := ⟨M, hM.isPrime, hM0⟩
  refine ⟨P, hlP, ?_⟩
  have hiff : (∃ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 ∧ (l : OF E) ∈ v.asIdeal) ↔
      (∃ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal ∧ v.asIdeal ∣ 𝔣) :=
    ⟨fun ⟨v, a, b⟩ => ⟨v, b, a⟩, fun ⟨v, a, b⟩ => ⟨v, b, a⟩⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.cNum_vp c_vp
  by_cases h : ∃ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 ∧ (l : OF E) ∈ v.asIdeal
  · rw [if_pos h, if_pos (hiff.1 h)]
    have hc : GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.condExp 𝔣 l = a0 𝔣 l := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.condExp a0
      congr 1
    rw [hc]
    push_cast
    rfl
  · rw [if_neg h, if_neg (mt hiff.2 h)]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.diffExp_vp GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.delta_vp
    rw [GlobalTheory.DifferentElement.mult_ratio E l hl P.asIdeal P.isPrime hlP,
      show padicValInt l (discr E) = padicValNat l (discr E).natAbs from rfl, Nat.factorization_def _ hl]
    push_cast
    rfl

end GlobalTheory.CNumAtPrime
end
end

