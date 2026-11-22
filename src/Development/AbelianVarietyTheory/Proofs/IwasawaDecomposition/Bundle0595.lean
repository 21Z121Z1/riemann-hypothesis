import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0177
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0057
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantLogarithm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompactRepresentativesModTorusPoints
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam GlobalTheory.ShFam.BdArc
  Filter Topology
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.PeriodSpan GlobalTheory.Points GlobalTheory.IntegralPower

namespace GlobalTheory.TorusCocompact

theorem exists_isCompact_surjOn {V H : Type} [NormedAddCommGroup V] [ProperSpace V] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CompactSpace H] [T2Space H] (φ : V → H) (hφ : ∀ z w, φ (z + w) = φ z * φ w)
    (hs : Function.Surjective φ) (hc : Continuous φ) : ∃ C : Set V, IsCompact C ∧ ∀ z, ∃ c ∈ C, φ (z - c) = 1 := by
  let ψ : V →+ Additive H := AddMonoidHom.mk' (fun z => Additive.ofMul (φ z)) hφ
  have : BaireSpace (Additive H) := inferInstanceAs (BaireSpace H)
  have : T2Space (Additive H) := inferInstanceAs (T2Space H)
  have ho : IsOpenMap φ := AddMonoidHom.isOpenMap_of_sigmaCompact ψ hs hc
  obtain ⟨n, hn⟩ := isCompact_univ.elim_directed_cover (fun n : ℕ => φ '' Metric.ball 0 n)
    (fun n => ho _ Metric.isOpen_ball) (fun h _ => by
      obtain ⟨z, rfl⟩ := hs h
      obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
      exact Set.mem_iUnion.2 ⟨n, z, by simpa using hn, rfl⟩)
    (Monotone.directed_le fun m n h => Set.image_mono (Metric.ball_subset_ball (Nat.cast_le.2 h)))
  refine ⟨Metric.closedBall 0 n, isCompact_closedBall _ _, fun z => ?_⟩
  obtain ⟨c, hc, hcz⟩ := hn (Set.mem_univ (φ z))
  refine ⟨c, Metric.ball_subset_closedBall hc, ?_⟩
  have h := hφ (z - c) c
  rw [sub_add_cancel, hcz] at h
  exact (mul_eq_right.1 h.symm)

theorem exists_lift_point {A B : Over (Sp ℂ)} (q : A ⟶ B) [Surjective q.left] [LocallyOfFiniteType q.left]
    (w : Over.mk (𝟙 (Sp ℂ)) ⟶ B) : ∃ u : Over.mk (𝟙 (Sp ℂ)) ⟶ A, u ≫ q = w := by
  let w' : Sp ℂ ⟶ B.left := w.left
  obtain ⟨z, -⟩ := (pullback.snd q.left w').surjective (IsLocalRing.closedPoint ℂ)
  obtain ⟨x, hx, -⟩ := GlobalTheory.ComplexPoints.exists_point_mem (pullback.snd q.left w') isClosed_univ.isLocallyClosed
    ⟨z, trivial⟩
  have h : (x ≫ pullback.fst q.left w') ≫ q.left = w' := by
    rw [Category.assoc, pullback.condition, reassoc_of% hx]
  refine ⟨Over.homMk (x ≫ pullback.fst q.left w') ?_, Over.OverMorphism.ext h⟩
  rw [← Over.w q, ← Category.assoc]
  exact (congrArg (· ≫ B.hom) h).trans (Over.w w)

section Fibre

variable {X : Scheme.{0}} {G : Over X} {y : Sp ℂ ⟶ X}

def fibrePt (x : Over.mk y ⟶ G) : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback y).obj G :=
  Over.homMk (pullback.lift x.left (𝟙 (Sp ℂ)) ((Over.w x).trans (Category.id_comp y).symm))
    (pullback.lift_snd _ _ _)

theorem fibrePt_fst (x : Over.mk y ⟶ G) : (fibrePt x).left ≫ pullback.fst G.hom y = x.left :=
  pullback.lift_fst _ _ _

theorem fibre_ext {u v : Over.mk (𝟙 (Sp ℂ)) ⟶ (Over.pullback y).obj G}
    (h : u.left ≫ pullback.fst G.hom y = v.left ≫ pullback.fst G.hom y) : u = v :=
  Over.OverMorphism.ext (pullback.hom_ext h ((Over.w u).trans (Over.w v).symm))

theorem fibrePt_surjective : Function.Surjective (fibrePt (G := G) (y := y)) := fun u =>
  ⟨Over.homMk (u.left ≫ pullback.fst G.hom y) (by
    have h : u.left ≫ pullback.snd G.hom y = 𝟙 _ := Over.w u
    rw [Category.assoc, pullback.condition, reassoc_of% h]
    rfl), fibre_ext (fibrePt_fst _)⟩

theorem fibrePt_mul [GrpObj G] (a b : Over.mk y ⟶ G) : fibrePt (a * b) = fibrePt a * fibrePt b := by
  let U : Over.mk ((Over.mk (𝟙 (Sp ℂ))).hom ≫ y) ⟶ Over.mk y := Over.homMk (𝟙 (Sp ℂ)) rfl
  have hU : ∀ x : Over.mk y ⟶ G, (U ≫ x).left = x.left := fun x => Category.id_comp _
  refine fibre_ext ?_
  rw [fibrePt_fst, ← (isGrpPullback_pullback G y).2 _ (fibrePt a) (fibrePt b) (U ≫ a) (U ≫ b)
    ((hU a).trans (fibrePt_fst a).symm) ((hU b).trans (fibrePt_fst b).symm), ← comp_mul, hU]

theorem continuous_fibrePt {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (e : V → (Over.mk y ⟶ G))
    (he : IsHolTo Set.univ (fun z => (e z).left)) :
    Continuous fun z => leftPt (𝟙 (Sp ℂ)) (fibrePt (e z)) := by
  have h1 : Continuous fun z => leftPt y (e z) := by
    refine GlobalTheory.Points.continuous_iff.2 fun U => ⟨?_, fun f => ?_⟩
    · simpa using (he U 0).1
    · exact (he U f).2.continuousOn.mono fun _ hb => ⟨trivial, hb⟩
  refine (isEmbedding_of_isPullback (C := ℂ) (IsPullback.of_hasPullback G.hom y)).continuous_iff.2 ?_
  refine (h1.prodMk (continuous_const (y := 𝟙 (Sp ℂ)))).congr fun z => ?_
  exact Prod.ext (fibrePt_fst (e z)).symm (Over.w (fibrePt (e z))).symm

end Fibre

attribute [local instance] ptTopology in

theorem exists_isCompact_mod_torusPts : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (g : ℕ)
    (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (E : TorusExtension ((Over.pullback y).obj G)), IsSemiAbelian G →
    (∀ z w, e (z + w) = e z * e w) → Function.Surjective e → IsHolTo Set.univ (fun z => (e z).left) →
    (∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
      ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) →
    ∃ C : Set (Fin g → ℂ), IsCompact C ∧ ∀ z, ∃ c ∈ C, e (z - c) ∈ torusPts G y E := by
  intro X G _ y g e E hG hadd hsurj hhol _
  let := E.addCommGroup
  let := E.grpB
  have := E.q_hom
  have := E.q_surjective
  have := E.isAbelian.proper
  have := hG.smooth
  have : LocallyOfFiniteType (E.q.left ≫ E.B.hom) := by
    rw [Over.w E.q]
    exact inferInstanceAs (LocallyOfFiniteType (pullback.snd G.hom y))
  have : LocallyOfFiniteType E.q.left := locallyOfFiniteType_of_comp _ E.B.hom
  have : CompactSpace (PtsOver E.B.hom (𝟙 (Sp ℂ))) := GlobalTheory.ProperPoints.compactSpace_pts E.B.hom
  have := compactSpace_of_ptsOver (𝟙 (Sp ℂ)) E.B
  have := isTopologicalGroup (𝟙 (Sp ℂ)) E.B
  have : T2Space (Over.mk (𝟙 (Sp ℂ)) ⟶ E.B) :=
    have := PtsOver.t2Space E.B.hom (𝟙 (Sp ℂ))
    T2Space.of_injective_continuous (f := fun x => (⟨x.left, Over.w x⟩ : PtsOver E.B.hom (𝟙 (Sp ℂ))))
      (fun _ _ h => Over.OverMorphism.ext (congrArg Subtype.val h))
      ((isEmbedding_leftPt (𝟙 (Sp ℂ)) E.B).continuous.subtype_mk _)
  obtain ⟨C, hC, H⟩ := exists_isCompact_surjOn (fun z => fibrePt (e z) ≫ E.q)
    (fun z w => by rw [hadd, fibrePt_mul, mul_comp])
    (fun w => by
      obtain ⟨u, rfl⟩ := exists_lift_point E.q w
      obtain ⟨x, rfl⟩ := fibrePt_surjective u
      obtain ⟨z, rfl⟩ := hsurj x
      exact ⟨z, rfl⟩)
    ((continuous_comp_over _ E.q).comp ((isEmbedding_leftPt _ _).continuous_iff.2 (continuous_fibrePt e hhol)))
  refine ⟨C, hC, fun z => ?_⟩
  obtain ⟨c, hc, hz⟩ := H z
  refine ⟨c, hc, E.isKernel.lift (fibrePt (e (z - c))) (toUnit _) hz, ?_⟩
  rw [IsPullback.lift_fst]
  exact fibrePt_fst _

end GlobalTheory.TorusCocompact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverse
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.ExpDirs

open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc ReciprocityTheory.ChartRestriction.G.PullbackSections Filter
open ReciprocityTheory.ChartRestriction.G.Chart (IsUnivChart sp)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem isDerivAt0_of_comb {X : Scheme.{0}} {t : SAB H X} {x : Sp ℂ ⟶ X} {g m : ℕ}
    {e : (Fin g → ℂ) → (Sp ℂ ⟶ t.G.left)} (e0 : e 0 = (1 : Over.mk x ⟶ t.G).left)
    {v : Fin m → (Sp (DualNumber ℂ) ⟶ t.G.left)} {w : Fin m → Fin g → ℂ} (ht : ∀ i, IsTanAtG t x (v i))
    (hv : ∀ i, IsDerivAt0 e (w i) (v i)) {a : Fin m → ℂ} {v' : Sp (DualNumber ℂ) ⟶ t.G.left} (ht' : IsTanAtG t x v')
    (hc : IsCombAtG t x v a v') : IsDerivAt0 e (∑ i, a i • w i) v' := by
  refine ⟨ht'.2.trans e0.symm, fun U h f => ?_⟩
  have hU : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U := fun i => DerLin.le_of_fst_eq ((ht i).2.trans ht'.2.symm) h
  let b : Fin m → TanMod.TanSp x t.G := fun i =>
    TanMod.TanSp.mk (Over.homMk (v i) (ht i).1) (TanMod.smT_zero_of x _ (ht i).2)
  have key : (TanDeriv.evAt v' U h f).snd = ∑ i, a i * (TanDeriv.evAt (v i) U (hU i) f).snd := by
    refine TanDeriv.derivAt_sum b a v' ?_ U h hU f
    obtain ⟨u, hu, rfl⟩ := hc
    have hub : u = fun i => (a i • b i).pt := funext fun i => Over.OverMorphism.ext (hu i)
    subst hub
    rw [List.prod_ofFn, ← TanMod.TanSp.pt_sum]
  refine key.trans ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  exact congrArg (a i * ·) ((hv i).2 U (hU i) f)

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {σ : c.F →+* ℂ}

theorem frame_basis {x : Sp ℂ ⟶ Z.X} (f : EigFrame Z σ x) {n : ℕ}
    {xc : ∀ m : ℕ, sp (R₀ := ℂ) (ReciprocityTheory.ChartRestriction.G.Chart.JetR ℂ (Fin n) m) ⟶ (Over.pullback x).obj Z.t.G}
    (hx : IsUnivChart _ n xc) (cc : Letter Dw → Fin n → ℂ) (hcc : ∀ z, f.v z.1 z.2 = vec Z.t x xc (cc z)) :
    LinearIndependent ℂ cc ∧ ⊤ ≤ Submodule.span ℂ (Set.range cc) := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨p, hp, hps⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hE : ∀ τ m, IsEigV (rho hx) (embK c τ) m ↔ ∀ a : 𝓞 E, vec Z.t x xc m ≫ (Z.t.act.act a).left =
      spMap (epsMul (σ (embK c τ a))) ≫ vec Z.t x xc m := fun τ m => by
    rw [vec_eig_iff hx (fun a => σ (embK c τ a)), ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
    rfl
  have hv : ∀ τ, f.v τ = fun i => vec Z.t x xc (cc ⟨τ, i⟩) := fun τ => funext fun i => hcc ⟨τ, i⟩
  have hb : ∀ τ m, IsEigV (rho hx) (embK c τ) m → ∃! a : Fin (Dw.mult τ) → ℂ, m = ∑ i, a i • cc ⟨τ, i⟩ :=
    fun τ m hm => by
      have := f.basis τ _ (vec_tan hx m) ((hE τ m).1 hm)
      rw [hv] at this
      simpa only [LieLocBasis.comb_iff hx] using this
  have he : ∀ τ (a : Fin (Dw.mult τ) → ℂ), IsEigV (rho hx) (embK c τ) (∑ i, a i • cc ⟨τ, i⟩) := fun τ a r => by
    have h1 : ∀ i, IsEigV (rho hx) (embK c τ) (cc ⟨τ, i⟩) := fun i => (hE _ _).2 (hcc ⟨τ, i⟩ ▸ f.eig τ i)
    rw [map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, h1 i r, smul_comm]
  refine ⟨Fintype.linearIndependent_iff.2 fun a ha z => ?_, fun m _ => ?_⟩
  · rw [Fintype.sum_sigma] at ha
    have h1 := proj_sum_eig (rho hx) (embK c) α hinj _ (fun τ => he τ fun i => a ⟨τ, i⟩) z.1
    rw [ha, map_zero] at h1
    exact congrFun ((hb z.1 0 fun r => by simp).unique h1 (y₂ := 0) (by simp)) z.2
  · have h1 := LinearMap.congr_fun (sum_proj (rho hx) (embK c) α hinj) m
    rw [LinearMap.sum_apply, Module.End.one_apply] at h1
    rw [← h1]
    refine Submodule.sum_mem _ fun τ _ => ?_
    obtain ⟨a, ha, -⟩ := hb τ _ (eig_of_alpha _ _ α hN τ (proj_eig_alpha (rho hx) _ α hinj p hp hps τ m))
    rw [ha]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem dirs_basis {x : Sp ℂ ⟶ Z.X} (f : EigFrame Z σ x) {g : ℕ} {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left)}
    (e0 : e 0 = (1 : Over.mk x ⟶ Z.t.G).left) (h1 : ∀ w, ∃! v, IsTanAtG Z.t x v ∧ IsDerivAt0 e w v)
    (h2 : ∀ v, IsTanAtG Z.t x v → ∃! w, IsDerivAt0 e w v) {W : Letter Dw → Fin g → ℂ}
    (hW : ∀ z, IsDerivAt0 e (W z) (f.v z.1 z.2)) : ∃ b : Module.Basis (Letter Dw) ℂ (Fin g → ℂ), ⇑b = W := by
  classical
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t x
  choose cc hcc using fun z : Letter Dw => vec_exists hx _ (f.tan z.1 z.2)
  obtain ⟨hli, hsp⟩ := frame_basis f hx cc hcc
  choose u hu using fun j : Fin n => (h2 _ (vec_tan hx (Pi.single j 1))).exists
  let T : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Fintype.linearCombination ℂ u
  have hT : ∀ m, IsDerivAt0 e (T m) (vec Z.t x xc m) := fun m =>
    isDerivAt0_of_comb e0 (fun j => vec_tan hx _) hu (vec_tan hx m) ((LieLocBasis.comb_iff hx _ m m).2 (by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]))
  have hbij : Function.Bijective T := by
    refine ⟨fun m m' h => vec_inj hx ((h1 (T m)).unique ⟨vec_tan hx m, hT m⟩ ⟨vec_tan hx m', h ▸ hT m'⟩), fun w => ?_⟩
    obtain ⟨v, ⟨hv, hd⟩, -⟩ := h1 w
    obtain ⟨m, rfl⟩ := vec_exists hx v hv
    exact ⟨m, (h2 _ hv).unique (hT m) hd⟩
  refine ⟨(Module.Basis.mk hli hsp).map (LinearEquiv.ofBijective T hbij), funext fun z => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.mk_apply]
  exact (h2 _ (f.tan z.1 z.2)).unique (hcc z ▸ hT (cc z)) (hW z)

theorem differentiableAt_dir {n g : ℕ} {e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)}
    {ex : ExpMaps Z σ g} (he : IsExpChart e ex) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {B : Set V} (hB : IsOpen B) {x : V → CxPts (genStr Z) σ}
    (hx : IsHolTo B fun b => (x b).1) (hs : ∀ b ∈ B, x b ∈ e.source) {v : V → (Sp (DualNumber ℂ) ⟶ Z.t.G.left)}
    (hv : HolTan B v) {W : V → Fin g → ℂ} (hW : ∀ b ∈ B, IsDerivAt0 (fun w => (ex (x b) w).left) (W b) (v b))
    {b₀ : V} (hb₀ : b₀ ∈ B) : DifferentiableAt ℂ W b₀ := by
  obtain ⟨-, h1, -, h3, h4, h5⟩ := he
  let ε : CxPts (genStr Z) σ → (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left) := fun y w => (ex y w).left
  have hz : DifferentiableAt ℂ (fun b => e (x b)) b₀ :=
    differentiableAt_pi.2 fun k => (h1 k V B x hB hx hs).differentiableAt (hB.mem_nhds hb₀)
  have ht := e.map_source (hs b₀ hb₀)
  have hl : ∀ b ∈ B, ε (e.symm (e (x b))) = ε (x b) := fun b hb => by rw [e.left_inv (hs b hb)]
  refine HolLieFrame.differentiableAt_of_forms _ b₀ fun w hw => ?_
  have hw' : ∀ (U : Z.t.G.left.Opens) (f : Γ(Z.t.G.left, U)), ⊤ ≤ ε (x b₀) 0 ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (ε (x b₀) z) U f) 0 w = 0 := by
    intro U f hU
    have hU' : ⊤ ≤ ε (e.symm (e (x b₀))) 0 ⁻¹ᵁ U := by rwa [hl b₀ hb₀]
    have d := (HolLieFrame.differentiableAt_fderiv (e := fun z => ε (e.symm z)) h4 ht U f hU').comp b₀ hz
    have hn : ∀ᶠ b in 𝓝 b₀, b ∈ B ∧ ⊤ ≤ v b ⁻¹ᵁ U := by
      have hc : ContinuousAt (fun b => (e (x b), (0 : Fin g → ℂ))) b₀ := hz.continuousAt.prodMk continuousAt_const
      filter_upwards [hB.mem_nhds hb₀, hc.preimage_mem_nhds ((h4 U f).1.mem_nhds ⟨⟨ht, trivial⟩, hU'⟩)] with b hb hb'
      have h' : ⊤ ≤ ε (e.symm (e (x b))) 0 ⁻¹ᵁ U := hb'.2
      rw [hl b hb] at h'
      exact ⟨hb, (TangentOrigin.top_le_preimage_iff _ U).2 (by rw [(hW b hb).1]; exact h')⟩
    refine hw (fun b => fderiv ℂ (fun z => valAt' (ε (x b) z) U f) 0) (d.congr_of_eventuallyEq ?_)
      (((hv U f).differentiableAt hn).congr_of_eventuallyEq ?_)
    · filter_upwards [hB.mem_nhds hb₀] with b hb
      simp only [Function.comp_apply, hl b hb]
    · filter_upwards [hn] with b ⟨hb, h⟩
      refine ((hW b hb).2 U h f).symm.trans ?_
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR, dif_pos h]
  have d₁ := LocalLift.isDerivAt0_const (ε (x b₀)) w hw'
  have d₀ := LocalLift.isDerivAt0_const (ε (x b₀)) 0 fun _ _ _ => map_zero _
  have e0 : ex (x b₀) 0 = 1 := by simpa using h3 _ (hs b₀ hb₀) 0 0
  exact ((h5 _ (hs b₀ hb₀)).2 _ ⟨(Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Over.w (ex (x b₀) 0))),
    d₁.1.trans (congrArg (·.left) e0)⟩).unique d₁ d₀

theorem exists_inverse {J : Type} [Fintype J] [DecidableEq J] {g : ℕ} (b : Module.Basis J ℂ (Fin g → ℂ)) :
    ∃ Wi : Matrix (Fin g) J ℂ, Matrix.of b * Wi = 1 ∧ Wi * Matrix.of b = 1 := by
  refine ⟨Matrix.of fun j z => b.repr (Pi.single j 1) z, ?_, ?_⟩
  · ext z z'
    have h : b z = ∑ j, b z j • (Pi.single j 1 : Fin g → ℂ) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    have h2 := congrArg (fun w => b.repr w z') h
    simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.finset_sum_apply,
      Finsupp.smul_apply, smul_eq_mul] at h2
    rw [Matrix.mul_apply, Matrix.one_apply, h2]
    rfl
  · ext j k
    have h := congrFun (b.sum_repr (Pi.single j 1)) k
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Finset.sum_apply, Pi.single_apply, eq_comm] using h

theorem exists_dirs_continuousOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n g : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g), IsExpChart e ex → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, (a b).1 ∈ e.source) → ∃ (W : V → Matrix (Letter Dw) (Fin g) ℂ) (Wi : V → Matrix (Fin g) (Letter Dw) ℂ), ContinuousOn W B ∧ ContinuousOn Wi B ∧ ∀ b ∈ B, Dirs (a b) (fun w => (ex (a b).1 w).left) (W b) ∧ W b * Wi b = 1 ∧ Wi b * W b = 1 := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ n g e ex he V _ _ _ B a hB ha hs
  have h5 := fun b hb => he.2.2.2.2.2 _ (hs b hb)
  choose! W hW using fun b hb (z : Letter Dw) => ((h5 b hb).2 _ ((a b).2.tan z.1 z.2)).exists
  have hbas : ∀ b ∈ B, ∃ bs : Module.Basis (Letter Dw) ℂ (Fin g → ℂ), ⇑bs = W b := fun b hb => by
    have e0 : ex (a b).1 0 = 1 := by simpa using he.2.2.2.1 _ (hs b hb) 0 0
    exact dirs_basis (a b).2 (e := fun w => (ex (a b).1 w).left) (congrArg (·.left) e0) (h5 b hb).1 (h5 b hb).2 (hW b hb)
  have hinv : ∀ b ∈ B, ∃ Wi : Matrix (Fin g) (Letter Dw) ℂ, Matrix.of (W b) * Wi = 1 ∧ Wi * Matrix.of (W b) = 1 :=
    fun b hb => by
      obtain ⟨bs, h⟩ := hbas b hb
      rw [← h]
      exact exists_inverse bs
  choose! Wi hWi using hinv
  have hd : ∀ b ∈ B, ∀ z, DifferentiableAt ℂ (fun b => W b z) b := fun b hb z =>
    differentiableAt_dir he hB ha.1 hs (ha.2 z.1 z.2) (fun b hb => hW b hb z) hb
  refine ⟨fun b => Matrix.of (W b), Wi, fun b hb => ContinuousAt.continuousWithinAt ?_,
    fun b hb => ContinuousAt.continuousWithinAt ?_, fun b hb => ⟨hW b hb, hWi b hb⟩⟩
  · exact continuousAt_pi.2 fun z => (hd b hb z).continuousAt
  · obtain ⟨bs, -⟩ := hbas b hb
    let q : Fin g ≃ Letter Dw := (Pi.basisFun ℂ (Fin g)).indexEquiv bs
    refine continuousAt_pi.2 fun j => continuousAt_pi.2 fun z => ?_
    have := HolFrameMatrix.differentiableAt_of_mul_eq_one (fun b => (Wi b).submatrix id q)
      (fun b => (Matrix.of (W b)).submatrix q id) b (fun i k => differentiableAt_pi.1 (hd b hb (q i)) k) (by
        filter_upwards [hB.mem_nhds hb] with b' hb'
        rw [Matrix.submatrix_mul_equiv, (hWi b' hb').2]
        rfl) j (q.symm z)
    simpa using this.continuousAt

end GlobalTheory.ShFam.Hor.ExpDirs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfIsGrpPullback
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.LieMet
  GlobalTheory.LocM
open GlobalTheory.Conormal
open GlobalTheory.Twist (resM resM_self)
open GlobalTheory.QCoh (pullbackSections)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO ptMap LieG dualScale)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.TanPair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {R : Type} [CommRing R] {x : Sp R ⟶ X} {G' : Over (Sp R)} [GrpObj G'] {φ : G'.left ⟶ t.G.left}
  (h' : IsGrpPullback G' t.G x φ)

theorem toUnit_specO_left : (toUnit (specO R R)).left = 𝟙 (Sp R) := by
  rw [Over.toUnit_left]
  exact Spec.map_id _

include h'

theorem exists_lieG {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    ∃ p : LieG G', p.1.left ≫ φ = v := by
  let p : specO R (DualNumber R) ⟶ G' :=
    Over.homMk (h'.1.lift v (specO R (DualNumber R)).hom hv.1) (h'.1.lift_snd _ _ _)
  have hp : p.left ≫ φ = v := h'.1.lift_fst _ _ _
  refine ⟨⟨p, Over.OverMorphism.ext (h'.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))⟩, hp⟩
  rw [Over.comp_left, Over.comp_left, toUnit_specO_left, Category.assoc, hp, Category.assoc]
  exact (epsZero_comp_of_isTanAtG t hv).trans ((unitSec_comp h').symm.trans (Category.id_comp _).symm)

theorem isTanAtG_lieG (p : LieG G') : IsTanAtG t x (p.1.left ≫ φ) := by
  constructor
  · rw [Category.assoc, h'.1.w, ← Category.assoc]
    exact congrArg (· ≫ x) (Over.w p.1)
  · rw [← Category.assoc, Hom.one_def, Over.comp_left, Over.toUnit_left]
    exact (congrArg (· ≫ φ) (sec_epsZero_comp p)).trans (unitSec_comp h')

theorem tanForm_eq (p : LieG G') {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v) (hp : p.1.left ≫ φ = v) :
    tanForm t hv = omegaBase h' ≫ cotMap p.1 (epsZero_comp p) ≫ (epsIso R).hom := by
  refine Eq.trans (congrArg (· ≫ (epsIso R).hom) ?_) (Category.assoc _ _ _)
  refine pullback_hom_ext (sec_hom η[t.G]) fun W a => ?_
  have k₁ : x ⁻¹ᵁ unitSec t.G ⁻¹ᵁ W ≤ unitSec G' ⁻¹ᵁ φ ⁻¹ᵁ W :=
    (le_preimage_of_comp (unitSec_comp h')).2 le_rfl
  have k₂ : x ⁻¹ᵁ unitSec t.G ⁻¹ᵁ W ≤ sec (epsZero R) ⁻¹ᵁ v ⁻¹ᵁ W :=
    (le_preimage_of_comp (epsZero_comp_of_isTanAtG t hv)).2 le_rfl
  have k₃ : v ⁻¹ᵁ W ≤ p.1.left ⁻¹ᵁ φ ⁻¹ᵁ W := (le_preimage_of_comp hp).2 le_rfl
  refine (baseMap_d (sec_hom η[t.G]) (sec_hom (epsZero R)) hv.1 (epsZero_comp_of_isTanAtG t hv) le_rfl le_rfl k₂
    le_rfl a).trans ?_
  refine Eq.symm ((congrArg ((cotMap p.1 (epsZero_comp p)).app _)
    (omegaBase_dUnit h' le_rfl le_rfl k₁ le_rfl a)).trans ?_)
  exact (cotMap_d p.1 (epsZero_comp p) k₁ k₂ k₃ _).trans (congrArg _ (appLE_appLE hp _ _ _ a))

theorem tanEv_eq (p : LieG G') {v : Sp (DualNumber R) ⟶ t.G.left} (hv : IsTanAtG t x v) (hp : p.1.left ≫ φ = v)
    {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) (s : Γ(omega t.G, V)) :
    tanEv t hv h s = (Scheme.ΓSpecIso (.of R)).hom
      (dualApp (tangent p) le_top ((omegaBase h').app ⊤ (pullbackSections x (omega t.G) h s))) := by
  rw [tanEv, tanForm_eq h' p hv hp]
  rfl

theorem exists_equiv_of_isGrpPullback {V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} {s : Fin n → Γ(omega t.G, V)}
    (hs : VB.IsFrame s) : ∃ Φ : TanM x t.G ≃ₗ[R] (Fin n → R), ∀ v b, Φ v b = tanEv t (isTan_tv v) h (s b) := by
  have := t.semi
  have : QuasiSeparated G'.hom := MorphismProperty.of_isPullback h'.1 inferInstance
  let e : Fin n → Γ(omega G', ⊤) := fun b => (omegaBase h').app ⊤ (pullbackSections x (omega t.G) h (s b))
  have he : VB.IsFrame e := by
    have h₁ := ((hs.pullback x).res h).map_iso (omegaBase h')
    have h₂ (b : Fin n) : resM _ h (pullbackSections x (omega t.G) le_rfl (s b)) =
        pullbackSections x (omega t.G) h (s b) := QCoh.res_pullbackSections x _ _ _ _
    simpa only [h₂] using h₁
  have hc := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).hom
  let Φ : TanM x t.G →ₗ[R] (Fin n → R) :=
    { toFun := fun v b => tanEv t (isTan_tv v) h (s b)
      map_add' := fun v w => funext fun b => by
        obtain ⟨p, hp⟩ := exists_lieG h' (isTan_tv v)
        obtain ⟨q, hq⟩ := exists_lieG h' (isTan_tv w)
        have hpq : (p.1 * q.1).left ≫ φ = (tv (v + w)).left :=
          (h'.2 _ p.1 q.1 (tv v) (tv w) hp.symm hq.symm).symm
        rw [Pi.add_apply, tanEv_eq h' p _ hp, tanEv_eq h' q _ hq,
          tanEv_eq h' ⟨_, OmegaGlobal.fst_mul p q⟩ _ hpq, tangent_mul, dualApp_add, LinearMap.add_apply, map_add]
      map_smul' := fun a v => funext fun b => by
        obtain ⟨p, hp⟩ := exists_lieG h' (isTan_tv v)
        have ha : (dualScale a).toRingHom = epsScaleR a := by
          ext y <;> simp [dualScale, epsScaleR]
        have hpq : (ptMap (dualScale a) ≫ p.1).left ≫ φ = (tv (a • v)).left := by
          rw [Over.comp_left, Category.assoc, hp]
          exact congrArg (fun r => spMap r ≫ (tv v).left) ha
        rw [Pi.smul_apply, tanEv_eq h' p _ hp, tanEv_eq h' ⟨_, OmegaGlobal.fst_scale a p⟩ _ hpq, tangent_scale]
        simp only [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, GlobalTheory.LB.resG_self,
          Iso.inv_hom_id_apply, RingHom.id_apply] }
  refine ⟨LinearEquiv.ofBijective Φ ⟨fun v w hvw => ?_, fun c => ?_⟩, fun _ _ => rfl⟩
  · obtain ⟨p, hp⟩ := exists_lieG h' (isTan_tv v)
    obtain ⟨q, hq⟩ := exists_lieG h' (isTan_tv w)
    obtain rfl : p = q := tangent_injective R G' (he.dual_ext le_rfl fun b => by
      rw [resM_self]
      exact hc.1 ((tanEv_eq h' p _ hp h (s b)).symm.trans
        ((congrFun hvw b).trans (tanEv_eq h' q _ hq h (s b)))))
    exact tan_ext (hp.symm.trans hq)
  · obtain ⟨p, hp⟩ := TangentSurj.tangent_surjective R G'
      ((he.dual.basis le_rfl).equivFun.symm fun b => cst R (c b))
    refine ⟨tanOf (isTanAtG_lieG h' p), funext fun b => (tanEv_eq h' p _ rfl h (s b)).trans ?_⟩
    have k := he.dual_basis_repr le_rfl (tangent p) b
    rw [resM_self, hp, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, ← hp] at k
    exact (congrArg _ k.symm).trans (Iso.inv_hom_id_apply _ _)

omit h'

theorem exists_tanM_equiv (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (n : ℕ)
    (s : Fin n → Γ(omega t.G, V)) (hs : VB.IsFrame s) :
    ∃ Φ : TanM x t.G ≃ₗ[R] (Fin n → R), ∀ v b, Φ v b = tanEv t (isTan_tv v) h (s b) :=
  exists_equiv_of_isGrpPullback (isGrpPullback_pullback t.G x) h hs

end GlobalTheory.LocM.TanPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantLogarithmStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_logarithm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (R : Frame X.Ψ N → ℂ), DifferentiableOn ℂ R X.dom → (∀ x ∈ X.dom, R x ≠ 0) → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ N, R (rmul x b) = R x) → ∃ L : Frame X.Ψ N → ℂ, DifferentiableOn ℂ L X.dom ∧ (∀ x ∈ X.dom, Complex.exp (L x) = R x) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ N, L (rmul x b) = L x) := by
  first | exact @GlobalTheory.FrameLog.exists_invariant_log | exact GlobalTheory.FrameLog.exists_invariant_log | (intros; apply GlobalTheory.FrameLog.exists_invariant_log <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroHermOfSkew
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem exists_herm_mulVec_self_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (G : Matrix (Fin N) (Fin N) E) (κ : E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → cc κ = -κ →
    κ ≠ 0 → ∀ n : Matrix (Fin N) (Fin N) E, IsSkew G n → n ≠ 0 → ∃ x, herm G (n.mulVec x) x ≠ 0 := by
  intro E _ _ _ N G κ _ hdet hκ hκ0 n _ hn
  by_contra hcon
  push_neg at hcon
  have pol : ∀ x y, herm G (n.mulVec x) y + herm G (n.mulVec y) x = 0 := by
    intro x y
    have h := hcon (x + y)
    rw [Matrix.mulVec_add, herm_add_left, herm_add_right, herm_add_right, hcon x, hcon y] at h
    linear_combination h
  have key : ∀ x y, herm G (n.mulVec x) y = 0 := by
    intro x y
    have h1 := pol (κ • x) y
    rw [Matrix.mulVec_smul, herm_smul_left, herm_smul_right, hκ] at h1
    have h2 := pol x y
    have h3 : (2 * κ) * herm G (n.mulVec x) y = 0 := by linear_combination h1 + κ * h2
    have h4 : (2 * κ : E) ≠ 0 := mul_ne_zero two_ne_zero hκ0
    exact (mul_eq_zero.1 h3).resolve_left h4
  apply hn
  rw [Matrix.ext_iff_mulVec]
  intro x
  rw [Matrix.zero_mulVec]
  exact eq_zero_of_herm G hdet _ (key x)

end GlobalTheory.UnipKill
end

