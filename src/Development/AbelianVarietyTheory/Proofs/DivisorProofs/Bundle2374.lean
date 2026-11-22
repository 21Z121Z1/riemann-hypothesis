import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2314
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2309
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2220
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2267
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingPullbackPowerMapLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_pullback_powerMap_level : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (H₀ : LB A.left) (P : LB (G2 A).left), IsAbelianScheme A → H₀.IsLB → Out.RelAmple A H₀ → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (m a b : ℕ) (n : ℤ) (T : Over S) (x₁ x₂ y₁ y₂ : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) (GlobalTheory.UPel.HT.Hecke.lbPow P m) n (lift (x₁ ^ a) (x₂ ^ b)) (lift (y₁ ^ a) (y₂ ^ b)) c → Out.WeilIs (G2 A) P (n * ((m * a * b : ℕ) : ℤ)) (lift x₁ x₂) (lift y₁ y₂) c := by
  first | (exact @GlobalTheory.HeckePullLevel.weilIs_powPull) | (exact GlobalTheory.HeckePullLevel.weilIs_powPull) | (intros; apply GlobalTheory.HeckePullLevel.weilIs_powPull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleReductionSystemMapImmersion
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem isClosedImmersion_subschemeι_comp {R : Type} [CommRing R] {W W' : Scheme.{0}}
    (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) [IsSeparated f] [IsImmersion π]
    (T : W'.IdealSheafData) [IsProper (T.subschemeι ≫ π ≫ f)] :
    IsClosedImmersion (T.subschemeι ≫ π) := by
  haveI : IsProper ((T.subschemeι ≫ π) ≫ f) := by rw [Category.assoc]; infer_instance
  haveI : IsProper (T.subschemeι ≫ π) := IsProper.of_comp _ f
  exact IsClosedImmersion.of_isPreimmersion _ (T.subschemeι ≫ π).isClosedMap.isClosed_range

theorem isProper_ker_subschemeι_comp {X Y S : Scheme.{0}} (g : X ⟶ Y) [IsClosedImmersion g]
    (f : Y ⟶ S) [IsProper (g ≫ f)] : IsProper (g.ker.subschemeι ≫ f) := by
  change IsProper (g.imageι ≫ f)
  have hg : g.imageι = inv g.toImage ≫ g := (IsIso.eq_inv_comp _).2 g.toImage_imageι
  rw [hg, Category.assoc]
  infer_instance

theorem mapSystem : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0})
    (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W), IsSeparated f → IsImmersion π →
    ∀ t : ℕ → W'.IdealSheafData, IsSystem (π ≫ f) I t → (∀ e, IsProper ((t e).subschemeι ≫ π ≫ f)) →
    IsSystem f I (fun e => (t e).map π) ∧ (∀ e, IsProper (((t e).map π).subschemeι ≫ f)) ∧
      ∀ e, ((t e).map π).comap π = t e := by
  intro R _ I W W' f π hf hπ t ht hp
  have hci : ∀ e, IsClosedImmersion ((t e).subschemeι ≫ π) := fun e =>
    haveI := hp e; isClosedImmersion_subschemeι_comp f π (t e)
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  ·
    show (t e).map π = (t (e + 1)).map π ⊔ baseIdeal f (I ^ (e + 1))
    have hle : t (e + 1) ≤ t e := by rw [ht e]; exact le_sup_left
    have hι : IsClosedImmersion (t (e + 1)).subschemeι := inferInstance
    have h1 : ((t e).comap (t (e + 1)).subschemeι).map (t (e + 1)).subschemeι = t e := by
      have := (GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion _ _ _ hι ⊥ (t e)).1
      rw [bot_sup_eq, Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι,
        sup_eq_right.2 hle] at this
      exact this
    have hbot : (t (e + 1)).comap (t (e + 1)).subschemeι = ⊥ := by
      have := (GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion _ _ _ hι ⊥ ⊥).2
      rwa [Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι] at this
    have h2 : (t e).comap (t (e + 1)).subschemeι =
        (baseIdeal f (I ^ (e + 1))).comap ((t (e + 1)).subschemeι ≫ π) := by
      conv_lhs => rw [ht e]
      rw [Scheme.IdealSheafData.comap_sup, hbot, bot_sup_eq, GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1, GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1,
        Category.assoc]
    have h3 := (GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion _ _ _ (hci (e + 1)) ⊥ (baseIdeal f (I ^ (e + 1)))).1
    rw [bot_sup_eq, Scheme.IdealSheafData.map_bot] at h3
    calc (t e).map π = (((t e).comap (t (e + 1)).subschemeι).map (t (e + 1)).subschemeι).map π := by
          rw [h1]
      _ = ((t e).comap (t (e + 1)).subschemeι).map ((t (e + 1)).subschemeι ≫ π) := by
          rw [Scheme.IdealSheafData.map_comp]
      _ = ((t (e + 1)).subschemeι ≫ π).ker ⊔ baseIdeal f (I ^ (e + 1)) := by rw [h2, h3]
      _ = (t (e + 1)).map π ⊔ baseIdeal f (I ^ (e + 1)) := rfl
  ·
    haveI := hci e
    haveI : IsProper (((t e).subschemeι ≫ π) ≫ f) := by rw [Category.assoc]; exact hp e
    exact isProper_ker_subschemeι_comp ((t e).subschemeι ≫ π) f
  ·
    haveI := hci e
    refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
    show t e ≤ (((t e).subschemeι ≫ π).ker).comap π
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    have h : pullback.fst π ((t e).subschemeι ≫ π) = pullback.snd _ _ ≫ (t e).subschemeι := by
      rw [← cancel_mono π, pullback.condition, Category.assoc]
    rw [h]
    conv_lhs => rw [← (t e).ker_subschemeι]
    exact Scheme.Hom.le_ker_comp _ _

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentDegreesSumLeTotalDegree
section
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

namespace GlobalTheory.Proof.componentDegrees_sum_le_total_degree

theorem degOn_sum_le : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ G : WTZ D.host.E, GoodW U (xiR D) V dict G → rankW U G = ∑ᶠ Z : Comp Xo c, rankOn U Z G ∧ (∑ᶠ Z : Comp Xo c, degOn U (xiR D) V dict Z G) ≤ degW U (xiR D) V dict G := by
  intro D H Dw l Xo c r U V dict hc G hG
  haveI : Finite (Comp Xo c) := finite_comp
  have hS : Splits U G := GlobalTheory.T.cuspForms_supLattice_split_over_components D H Dw l Xo c r U V dict (fun σ hσ => (hc.2 σ hσ).1) G
  have hO := GlobalTheory.T.components_peterssonOrthogonal_and_masses D H Dw l Xo c r U V dict hc G
  have hA : Adds U V dict G := GlobalTheory.T.component_ranks_degrees_add_with_masses D H Dw l Xo c r U V dict G hS hO.1
  obtain ⟨-, hr, -, -, hd⟩ := hA.2 hG
  refine ⟨hr, ?_⟩
  rw [hd]
  haveI : Fintype (Comp Xo c) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  refine Finset.sum_le_sum fun Z _ => ?_
  have hlog : (∑ σ : c.F →+* ℂ, Real.log (mass U V dict Z σ)) ≤ 0 :=
    Finset.sum_nonpos fun σ _ => Real.log_nonpos (hO.2.1 Z σ).1 (hO.2.1 Z σ).2
  have hq : ((∑ σ : c.F →+* ℂ, Real.log (mass U V dict Z σ)) / (Module.finrank ℚ c.F : ℝ)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hlog (Nat.cast_nonneg _)
  have hk : (0:ℝ) ≤ (rankOn U Z G : ℝ) / 2 := by positivity
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hk hq]

end GlobalTheory.Proof.componentDegrees_sum_le_total_degree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConductorSquareFlatBaseChangeSchemes
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch.FlatSq

open TensorProduct

theorem inj_of_isPushout {A B F G : Type} [CommRing A] [CommRing B] [CommRing F] [CommRing G]
    (f : A →+* F) (g : A →+* B) (h : F →+* G) (k : B →+* G)
    (sq : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom h) (CommRingCat.ofHom k))
    (hf : f.Flat) (hg : Function.Injective g) : Function.Injective h := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := h.toAlgebra
  letI := k.toAlgebra
  letI : Algebra A G := (h.comp f).toAlgebra
  haveI : IsScalarTower A F G := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A B G := IsScalarTower.of_algebraMap_eq (fun a => by
    have := congrArg (fun φ => (CommRingCat.Hom.hom φ) a) sq.w
    simpa [RingHom.algebraMap_toAlgebra] using this)
  haveI : Module.Flat A F := hf
  have hP : Algebra.IsPushout A F B G := (CommRingCat.isPushout_iff_isPushout).1 sq
  have hP' : Algebra.IsPushout A B F G := hP.symm
  rw [injective_iff_map_eq_zero]
  intro x hx
  have e1 : Algebra.IsPushout.equiv A B F G ((1 : B) ⊗ₜ x) = 0 := by
    rw [Algebra.IsPushout.equiv_tmul]; simpa [RingHom.algebraMap_toAlgebra] using hx
  have e2 : ((1 : B) ⊗ₜ[A] x) = 0 := by
    simpa using (Algebra.IsPushout.equiv A B F G).injective (e1.trans (map_zero _).symm)
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := F) (Algebra.linearMap A B) hg
  have e3 : LinearMap.rTensor F (Algebra.linearMap A B) ((1 : A) ⊗ₜ x) = 0 := by simpa using e2
  have e4 : ((1 : A) ⊗ₜ[A] x) = 0 := hinj (e3.trans (map_zero _).symm)
  simpa using congrArg (TensorProduct.lid A F) e4

end GlobalTheory.Pinch.FlatSq

namespace GlobalTheory.Pinch.FlatSq

open TensorProduct

theorem ideal_mul_of_isPushout {A B F G : Type} [CommRing A] [CommRing B] [CommRing F] [CommRing G]
    (f : A →+* F) (g : A →+* B) (h : F →+* G) (k : B →+* G)
    (sq : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom h) (CommRingCat.ofHom k))
    (J : Ideal A) (hJ : ∀ a ∈ J, ∀ b : B, ∃ a' ∈ J, g a' = g a * b) :
    ∀ x ∈ J.map f, ∀ r : G, ∃ y ∈ J.map f, h y = h x * r := by
  have hw : ∀ a, k (g a) = h (f a) := fun a => by
    have := congrArg (fun φ => (CommRingCat.Hom.hom φ) a) sq.w
    simpa using this.symm
  have hQ : ∀ x ∈ J.map f, ∀ b : B, ∃ y ∈ J.map f, h y = h x * k b := by
    intro x hx
    change x ∈ Ideal.span _ at hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      intro b
      obtain ⟨a', ha', e⟩ := hJ a ha b
      refine ⟨f a', Ideal.mem_map_of_mem f ha', ?_⟩
      rw [← hw, ← hw, e, map_mul]
    | zero => intro b; exact ⟨0, Ideal.zero_mem _, by simp⟩
    | add z w _ _ hz hw' =>
      intro b
      obtain ⟨y1, hy1, e1⟩ := hz b
      obtain ⟨y2, hy2, e2⟩ := hw' b
      exact ⟨y1 + y2, Ideal.add_mem _ hy1 hy2, by rw [map_add, e1, e2, map_add, add_mul]⟩
    | smul m z _ hz =>
      intro b
      obtain ⟨y1, hy1, e1⟩ := hz b
      refine ⟨m * y1, Ideal.mul_mem_left _ m hy1, ?_⟩
      rw [smul_eq_mul, map_mul, e1, map_mul]; ring
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := h.toAlgebra
  letI := k.toAlgebra
  letI : Algebra A G := (h.comp f).toAlgebra
  haveI : IsScalarTower A F G := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A B G := IsScalarTower.of_algebraMap_eq (fun a => (hw a).symm)
  have hP : Algebra.IsPushout A F B G := (CommRingCat.isPushout_iff_isPushout).1 sq
  have hP' : Algebra.IsPushout A B F G := hP.symm
  intro x hx r
  induction r using hP'.out.inductionOn with
  | zero => exact ⟨0, Ideal.zero_mem _, by simp⟩
  | tmul m =>
    refine ⟨x * m, Ideal.mul_mem_right _ _ hx, ?_⟩
    rw [map_mul]; rfl
  | smul b n hn =>
    obtain ⟨y1, hy1, e1⟩ := hn
    obtain ⟨y, hy, e⟩ := hQ y1 hy1 b
    refine ⟨y, hy, ?_⟩
    rw [e, e1, Algebra.smul_def, RingHom.algebraMap_toAlgebra]; ring
  | add n1 n2 h1 h2 =>
    obtain ⟨y1, hy1, e1⟩ := h1
    obtain ⟨y2, hy2, e2⟩ := h2
    exact ⟨y1 + y2, Ideal.add_mem _ hy1 hy2, by rw [map_add, e1, e2, mul_add]⟩

theorem ker_le_of_isPushout {A Q F G : Type} [CommRing A] [CommRing Q] [CommRing F] [CommRing G]
    (f : A →+* F) (q : A →+* Q) (h : F →+* G) (k : Q →+* G)
    (sq : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom q) (CommRingCat.ofHom h) (CommRingCat.ofHom k))
    (hq : Function.Surjective q) (x : F) (hx : h x = 0) : x ∈ (RingHom.ker q).map f := by
  letI := f.toAlgebra
  letI := q.toAlgebra
  letI := h.toAlgebra
  letI := k.toAlgebra
  letI : Algebra A G := (h.comp f).toAlgebra
  haveI : IsScalarTower A F G := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A Q G := IsScalarTower.of_algebraMap_eq (fun a => by
    have := congrArg (fun φ => (CommRingCat.Hom.hom φ) a) sq.w
    simpa [RingHom.algebraMap_toAlgebra] using this)
  have hP : Algebra.IsPushout A F Q G := (CommRingCat.isPushout_iff_isPushout).1 sq
  have hs : Function.Surjective (Algebra.ofId A Q) := hq
  let e1 := Algebra.TensorProduct.quotIdealMapEquivTensorQuot F (RingHom.ker (Algebra.ofId A Q))
  let e2 : F ⊗[A] (A ⧸ RingHom.ker (Algebra.ofId A Q)) ≃ₐ[A] F ⊗[A] Q :=
    Algebra.TensorProduct.congr AlgEquiv.refl (Ideal.quotientKerAlgEquivOfSurjective hs)
  let e3 := Algebra.IsPushout.equiv A F Q G
  have key : e3 (e2 (e1 (Ideal.Quotient.mk _ x))) = 0 := by
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
    simp only [e2, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgEquiv.coe_algHom, map_one]
    rw [Algebra.IsPushout.equiv_tmul]
    simpa [RingHom.algebraMap_toAlgebra] using hx
  have : Ideal.Quotient.mk (Ideal.map (algebraMap A F) (RingHom.ker (Algebra.ofId A Q))) x = 0 := by
    apply e1.injective; apply e2.injective; apply e3.injective
    rw [key]; simp
  rw [Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

end GlobalTheory.Pinch.FlatSq

namespace GlobalTheory.Pinch.FlatSq

theorem spMap_appLE_apply {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (e : (⊤ : (Sp R').Opens) ≤ spMap φ ⁻¹ᵁ ⊤) (a : Γ(Sp R, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of R')).hom (((spMap φ).appLE ⊤ ⊤ e).hom a) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom a) := by
  have h1 : (spMap φ).appLE ⊤ ⊤ e = (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  have := congrArg (fun t => t.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  rw [h1]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this

theorem cond_of_flat (R : Type) [CommRing R] (R' : Type) [CommRing R'] [Algebra R R']
    (hinj : Function.Injective (algebraMap R R')) (c : Ideal R)
    (hc : ∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r)
    (X X' Z : Scheme.{0}) (u : X ⟶ Sp R) (p : X' ⟶ X) (u' : X' ⟶ Sp R') (i : Z ⟶ X) (v : Z ⟶ Sp (R ⧸ c))
    (hu : Flat u) (hp : IsPullback p u' u (spMap (algebraMap R R')))
    (hi : IsPullback i v u (spMap (Ideal.Quotient.mk c))) : GlobalTheory.Pinch.Cond p i := by
  intro W hW
  have poP := (isIso_pushoutSection_iff hp (US := ⊤) (UT := ⊤) (UX := W) (UY := p ⁻¹ᵁ W) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen hp _ _ _ (isAffineOpen_top _)
    (isAffineOpen_top _) hW)
  have poZ := (isIso_pushoutSection_iff hi (US := ⊤) (UT := ⊤) (UX := W) (UY := i ⁻¹ᵁ W) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen hi _ _ _ (isAffineOpen_top _)
    (isAffineOpen_top _) hW)
  have hfl : (u.appLE ⊤ W le_top).hom.Flat :=
    HasRingHomProperty.appLE (P := @Flat) u hu ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  let eR := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  let eR' := (Scheme.ΓSpecIso (CommRingCat.of R')).commRingCatIsoToRingEquiv
  let eQ := (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ c))).commRingCatIsoToRingEquiv
  let gA := ((spMap (algebraMap R R')).appLE ⊤ ⊤ le_top).hom
  let qA := ((spMap (Ideal.Quotient.mk c)).appLE ⊤ ⊤ le_top).hom
  have hg : ∀ a, eR' (gA a) = algebraMap R R' (eR a) := fun a => spMap_appLE_apply _ _ a
  have hq : ∀ a, eQ (qA a) = Ideal.Quotient.mk c (eR a) := fun a => spMap_appLE_apply _ _ a
  have gA_inj : Function.Injective gA := by
    intro a b hab
    apply eR.injective; apply hinj
    rw [← hg, ← hg, hab]
  have qA_surj : Function.Surjective qA := by
    intro t
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (eQ t)
    refine ⟨eR.symm z, eQ.injective ?_⟩
    rw [hq, RingEquiv.apply_symm_apply, hz]
  let J := RingHom.ker qA
  have hJ : ∀ a ∈ J, ∀ b, ∃ a' ∈ J, gA a' = gA a * b := by
    intro a ha b
    have hx : eR a ∈ c := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hq, RingHom.mem_ker.1 ha, map_zero]
    obtain ⟨y, hy, e⟩ := hc (eR a) hx (eR' b)
    refine ⟨eR.symm y, ?_, eR'.injective ?_⟩
    · rw [RingHom.mem_ker]; apply eQ.injective
      rw [hq, RingEquiv.apply_symm_apply, map_zero, Ideal.Quotient.eq_zero_iff_mem]; exact hy
    · rw [hg, RingEquiv.apply_symm_apply, e, map_mul, hg]
  refine ⟨?_, ?_⟩
  · rw [Scheme.Hom.app_eq_appLE]
    exact inj_of_isPushout _ _ _ _ poP hfl gA_inj
  · intro x hx r
    rw [Scheme.Hom.app_eq_appLE] at hx
    have hxJ := ker_le_of_isPushout _ _ _ _ poZ qA_surj x hx
    obtain ⟨y, hy, e⟩ := ideal_mul_of_isPushout _ _ _ _ poP J hJ x hxJ r
    refine ⟨y, ?_, ?_⟩
    · rw [Scheme.Hom.app_eq_appLE]
      have hle : J.map (u.appLE ⊤ W le_top).hom ≤ RingHom.ker (i.appLE W (i ⁻¹ᵁ W) le_rfl).hom := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, RingHom.mem_ker]
        have := congrArg (fun φ => (CommRingCat.Hom.hom φ) a) poZ.w
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
        have h0 : qA a = 0 := RingHom.mem_ker.1 ha
        simp only [qA] at h0
        rw [this, h0, map_zero]
      exact hle hy
    · rw [Scheme.Hom.app_eq_appLE]; exact e

end GlobalTheory.Pinch.FlatSq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverFunctionFieldMapEqStatement
section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_function_field_map_eq : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y), ∃ hη : V.π (genericPoint V.G) ⤳ genericPoint Y.X, V.φ = GlobalTheory.TrueGeo.SmallSec.fnMap V.π hη := by
  first | exact @GlobalTheory.Mean4O.Cover.φ_eq_fnMap | exact GlobalTheory.Mean4O.Cover.φ_eq_fnMap | (intros; apply GlobalTheory.Mean4O.Cover.φ_eq_fnMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverStatementHoldsStatement
section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_statement_holds : CoverSt := by
  first | exact @GlobalTheory.FlatModel.coverSt_holds | exact GlobalTheory.FlatModel.coverSt_holds | (intros; apply GlobalTheory.FlatModel.coverSt_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineEqDeRhamOfSmoothLiftComparison
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.CrysLift

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def diagSec (X : Scheme.{0}) : AffOp X ⥤ (Pair (𝟙 X))ᵒᵖ :=
  (Monotone.functor (f := fun U : X.affineOpens ↦ (⟨(U, U), by simp⟩ : Pair (𝟙 X))) fun _ _ h ↦
      Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨h, h⟩)).op

def diagCoef (s : X ⟶ Sp R) : CoefMap (RingHom.id R) (OPair (𝟙 X) s) (OAff s) where
  G := diagSec X
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl

theorem diag_res_degree_one (s : X ⟶ Sp R) (c : HH1 s) :
    pullHyp1 (diagCoef s) (pullHyp1 (pairRes (𝟙 X) s) c) = c := by
  rw [← pullHyp1_comp]
  exact (pullHyp1_eq_of_natTrans _ (CoefMap.id _) { app U := 𝟙 U }
    (fun U b ↦ mp_id (OAff s) U b) c).trans (pullHyp1_id c)

theorem diag_res_degree_two (s : X ⟶ Sp R) (c : HH2 s) :
    pullHyp2 (diagCoef s) (pullHyp2 (pairRes (𝟙 X) s) c) = c := by
  rw [← pullHyp2_comp]
  exact (pullHyp2_eq_of_natTrans _ (CoefMap.id _) { app U := 𝟙 U }
    (fun U b ↦ mp_id (OAff s) U b) c).trans (pullHyp2_id c)

theorem eq_of_isPull1 {s : X ⟶ Sp R} (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) {c c' : HH1 s}
    (e : IsPull1 h c c') : c = c' := by
  have e' : pullHyp1 (pairRes (𝟙 X) s) c = pullHyp1 (pairRes (𝟙 X) s) c' :=
    (isPull1_id h c).symm.trans e
  rw [← diag_res_degree_one s c, e', diag_res_degree_one]

theorem eq_of_isPull2 {s : X ⟶ Sp R} (h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R)) {c c' : HH2 s}
    (e : IsPull2 h c c') : c = c' := by
  have e' : pullHyp2 (pairRes (𝟙 X) s) c = pullHyp2 (pairRes (𝟙 X) s) c' :=
    (isPull2_id h c).symm.trans e
  rw [← diag_res_degree_two s c, e', diag_res_degree_two]

theorem red_of {R₀ : Type} [CommRing R₀] {I : Ideal R} {π : R →+* R₀} (hπ : Function.Surjective π)
    (hI : RingHom.ker π = I) {X₀ : Scheme.{0}} {s : X ⟶ Sp R} {s₀ : X₀ ⟶ Sp R₀} {i : X₀ ⟶ X}
    (hp : IsPullback i s₀ s (spMap π)) :
    ∃ s₀' : X₀ ⟶ Sp (R ⧸ I), IsPullback i s₀' s (spMap (Ideal.Quotient.mk I)) ∧
      s₀ ≫ spMap π = s₀' ≫ spMap (Ideal.Quotient.mk I) := by
  subst hI
  let e := RingHom.quotientKerEquivOfSurjective hπ
  have he : (e : R ⧸ RingHom.ker π →+* R₀).comp (Ideal.Quotient.mk _) = π := RingHom.ext fun _ ↦ rfl
  have hs : spMap π = spMap (e : R ⧸ RingHom.ker π →+* R₀) ≫ spMap (Ideal.Quotient.mk _) := by
    conv_lhs => rw [← he]
    show Spec.map _ = Spec.map _ ≫ Spec.map _; rw [← Spec.map_comp]; rfl
  have : IsIso (CommRingCat.ofHom (e : R ⧸ RingHom.ker π →+* R₀)) := e.toCommRingCatIso.isIso_hom
  refine ⟨s₀ ≫ spMap (e : R ⧸ RingHom.ker π →+* R₀), ?_, by rw [hs, Category.assoc]⟩
  exact hp.of_iso (Iso.refl _) (Iso.refl _) (asIso (spMap (e : R ⧸ RingHom.ker π →+* R₀))) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp [hs])

end GlobalTheory.CrysLift

namespace GlobalTheory.CrysLift

open GlobalTheory.SmoothLift

theorem crystallineDeRham_of_smoothLift : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.CrystallineDeRham := by
  rintro ⟨e₁, e₂, -, -, hnat⟩ R _ I κ hκ R₀ _ π hπ hI X X₀ s s₀ i hs hsep hqc hp m
  have hid : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _
  have : IsIso (spMap (RingHom.id R)) := by rw [hid]; infer_instance
  let D : Data :=
    { R := R, I := ⊥, κ := dp0 R, nil := isDPNilpotent_bot R, X := X, X₀ := X, s := s, t := s, i := 𝟙 X,
      smooth := hs, sep := hsep, qc := hqc,
      red := by
        obtain ⟨s', h1, h2⟩ := red_of (π := RingHom.id R) Function.surjective_id
          ((RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id)
          (IsPullback.of_horiz_isIso (fst := 𝟙 X) (g := spMap (RingHom.id R)) (snd := s) (f := s)
            ⟨by rw [show spMap (RingHom.id R) = 𝟙 _ from Spec.map_id _, Category.id_comp, Category.comp_id]⟩)
        refine ⟨s', h1, ?_⟩
        rw [← h2, show spMap (RingHom.id R) = 𝟙 _ from Spec.map_id _, Category.comp_id] }
  let D' : Data :=
    { R := R, I := I, κ := κ, nil := hκ, X := X, X₀ := X₀, s := s, t := s₀ ≫ spMap π, i := i,
      smooth := hs, sep := hsep, qc := hqc,
      red := by
        obtain ⟨s', h1, h2⟩ := red_of hπ hI hp
        exact ⟨s', h1, h2⟩ }
  have h : 𝟙 X ≫ s = s ≫ spMap (RingHom.id R) := by
    rw [show spMap (RingHom.id R) = 𝟙 _ from Spec.map_id _, Category.id_comp, Category.comp_id]
  obtain ⟨h1, h2⟩ := hnat D D' (RingHom.id R) (𝟙 X) i h m (by simp [D, D'])
  have k1 : ∀ c, m.pull1 c = ((e₁ D).trans (e₁ D').symm) c := fun c ↦
    ((e₁ D').symm_apply_apply _).symm.trans (congrArg (e₁ D').symm (eq_of_isPull1 h (h1 c)).symm)
  have k2 : ∀ c, m.pull2 c = ((e₂ D).trans (e₂ D').symm) c := fun c ↦
    ((e₂ D').symm_apply_apply _).symm.trans (congrArg (e₂ D').symm (eq_of_isPull2 h (h2 c)).symm)
  exact ⟨(funext k1 : (⇑m.pull1 : _ → _) = _) ▸ ((e₁ D).trans (e₁ D').symm).bijective,
    (funext k2 : (⇑m.pull2 : _ → _) = _) ▸ ((e₂ D).trans (e₂ D').symm).bijective⟩

end GlobalTheory.CrysLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueEqFirstJetAlternatingProductStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cube_value_eq_first_jet_alternating_product : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g) (G : Geo ν d),
    (∀ (x y z : Fin g → ℂ) (j : thK.{0} → D.P.L.ι),
      (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ D.P.L.U (j I)) →
      valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
        (D.cub.t.s j).val = ∏ I : thK.{0}, G.frG (j I) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I) →
    ∀ (W : Fin g → ℂ) (gm : GtPt D (TE R ℂ)), (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) →
    IsD ν d W gm.b → ∀ (χ χ' : D.X) (x y : Fin g → ℂ),
    ν.eA (d.ex x) = DegPre.cF D ℂ χ → ν.eA (d.ex y) = DegPre.cF D ℂ χ' →
    vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
      1 + TrivSqZeroExt.inr
        (fderiv ℂ (G.frG (ν.J (ν.eA (d.ex (x + y))).left)) (x + y) W / G.frG (ν.J (ν.eA (d.ex (x + y))).left) (x + y) +
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex 0)).left)) 0 W / G.frG (ν.J (ν.eA (d.ex 0)).left) 0 -
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex x)).left)) x W / G.frG (ν.J (ν.eA (d.ex x)).left) x -
          fderiv ℂ (G.frG (ν.J (ν.eA (d.ex y)).left)) y W / G.frG (ν.J (ν.eA (d.ex y)).left) y) := by
  first | exact @GlobalTheory.MBLow.Cl.CubeJet.cube_jet | exact GlobalTheory.MBLow.Cl.CubeJet.cube_jet | (intros; apply GlobalTheory.MBLow.Cl.CubeJet.cube_jet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrLocalizationOfMinimalPrimeStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvr_localization_of_minimal_prime' : ∀ {κ : Type} [Field κ] (R : Subring κ) [IsNoetherianRing R] [IsIntegrallyClosed R] [IsFractionRing R κ] (Q : Ideal R) [Q.IsPrime], Q ≠ ⊥ → (∀ p : Ideal R, p.IsPrime → p ≠ ⊥ → p ≤ Q → p = Q) → ∃ W : ValuationSubring κ, IsDiscreteValuationRing W ∧ (∀ r : R, (r : κ) ∈ W) ∧ (∀ r : R, r ∉ Q → (r : κ)⁻¹ ∈ W) ∧ (∀ r : R, r ∈ Q → r ≠ 0 → (r : κ)⁻¹ ∉ W) ∧ (∀ w ∈ W, ∃ b s : R, s ∉ Q ∧ w = b / s) := by
  first | exact @GlobalTheory.exists_dvr_localization_of_minimal_prime | exact GlobalTheory.exists_dvr_localization_of_minimal_prime | (intros; apply GlobalTheory.exists_dvr_localization_of_minimal_prime <;> assumption)
end

