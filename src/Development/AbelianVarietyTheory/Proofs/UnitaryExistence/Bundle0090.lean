import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0085
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0087
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0089
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReduction
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChartCoverFOfSectionBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem ChartCover.exists_lift {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) :
    ∃ xF : Sp S ⟶ Xo.XF c, xF ≫ pullback.fst _ _ = w.x ∧ xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := by
  refine ⟨pullback.lift w.x (spMap (algebraMap c.F S)) ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  rw [w.x_over, spMap_comp_ring]
  rfl

theorem ChartCover.near (hS : Out.SecBaseChangeSt) {R A : Type} [CommRing R] [Algebra c.F R] [CommRing A]
    [Algebra c.F A] {j : Sp R ⟶ Xo.XF c} {y₀ : FrPt Xo c R} {π : R →ₐ[c.F] A}
    {X : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A} {s : Aˣ} {u : FrPt Xo c A}
    (hj : OpenChart j y₀) (hu : UnivFrame y₀ π X s u) {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S)
    (xF : Sp S ⟶ Xo.XF c) (h1 : xF ≫ pullback.fst _ _ = w.x)
    (h2 : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (p : Sp S) (hp : xF p ∈ Set.range j) :
    ∃ g : S, g ∉ p.asIdeal ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (lam : S →ₐ[c.F] T), IsUnit (lam g) →
      ∃ (z : FrPt Xo c T) (a : A →ₐ[c.F] T), FrMap lam w z ∧ FrMap a u z := by
  obtain ⟨g, hg, hT⟩ := openChart_factor_near_prime E H Dw l Xo c R j y₀ hj S xF h2 p hp
  refine ⟨g, hg, fun T _ _ lam hl => ?_⟩
  obtain ⟨ψ, hψ⟩ := hT T lam hl
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c S T lam w
  have hx : z.x = spMap ψ.toRingHom ≫ y₀.x := by
    rw [hz.1, ← h1, ← hj.2.1, ← Category.assoc, hψ, Category.assoc]
  obtain ⟨a, ⟨_, ha⟩, _⟩ := GlobalTheory.T.universalFrame_classifies_framedPoints hS E H Dw l Xo c R A y₀ π X s u hu T z ψ hx
  exact ⟨z, a, hz, ha⟩

theorem ChartCover.cls_loc (hS : Out.SecBaseChangeSt) {R : Type} [CommRing R] [Algebra c.F R] {A : TRing c.F}
    {j : Sp R ⟶ Xo.XF c} {y₀ : FrPt Xo c R} {π : R →ₐ[c.F] A.R}
    {X : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R} {s : (A.R)ˣ} {u : FrPt Xo c A.R}
    (hj : OpenChart j y₀) (hu : UnivFrame y₀ π X s u) {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S)
    (xF : Sp S ⟶ Xo.XF c) (h1 : xF ≫ pullback.fst _ _ = w.x)
    (h2 : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (m : Ideal S) [hm : m.IsPrime]
    (hp : xF (⟨m, hm⟩ : PrimeSpectrum S) ∈ Set.range j) :
    ∃ cw : A.R →ₐ[c.F] Localization.AtPrime m,
      ChartCls (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w m u cw ∧
      ChartLoc (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w m A u := by
  obtain ⟨g, hg, hT⟩ := ChartCover.near hS hj hu w xF h1 h2 (⟨m, hm⟩ : PrimeSpectrum S) hp
  obtain ⟨z, a, hz, ha⟩ := hT (Localization.AtPrime m) (locM c.F m)
    (IsLocalization.map_units (Localization.AtPrime m) (⟨g, hg⟩ : m.primeCompl))
  refine ⟨a, ⟨z, hz, ha⟩, ?_⟩
  intro p φ y hy
  obtain ⟨yF, k1, k2⟩ := ChartCover.exists_lift y
  have e : spMap φ.toRingHom ≫ yF = xF := by
    apply pullback.hom_ext
    · rw [Category.assoc, k1, h1, hy.1]
    · rw [Category.assoc, k2, h2, spMap_comp_ring]
      congr 1
      exact φ.comp_algebraMap
  have hq : yF (spMap φ.toRingHom (⟨m, hm⟩ : PrimeSpectrum S)) ∈ Set.range j := by
    rw [← e] at hp
    exact hp
  obtain ⟨g', hg', hT'⟩ := ChartCover.near hS hj hu y yF k1 k2 _ hq
  obtain ⟨p', lam, hl, hlam⟩ := GlobalTheory.testRing_localizationAway c.F p g'
  obtain ⟨z', a', hz', ha'⟩ := hT' p'.R lam hl
  exact ⟨g', hg', p', lam, z', a', hlam, hz', ha'⟩

end

theorem chartCoverF_of_secBaseChange : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ChartCoverF Xo c := by
  intro hS E _ _ _ H Dw l Xo c S _ _ w w' hw m hm
  obtain ⟨xF, h1, h2⟩ := ChartCover.exists_lift w
  obtain ⟨p, j, y₀, hj, hp⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hS E H Dw l Xo c (xF (⟨m, hm.isPrime⟩ : PrimeSpectrum S))
  obtain ⟨A, π, X, s, u, hu⟩ := GlobalTheory.T.exists_universalFrame_testRing hS E H Dw l Xo c p y₀
  obtain ⟨cw, hc, hl⟩ := ChartCover.cls_loc hS hj hu w xF h1 h2 m hp
  obtain ⟨cw', hc', hl'⟩ := ChartCover.cls_loc hS hj hu w' xF (h1.trans hw.symm) h2 m hp
  exact ⟨A, u, cw, cw', GlobalTheory.T.universalFrame_classifies_unique_openChart hS E H Dw l Xo c p.R A.R j y₀ π X s u hj hu,
    GlobalTheory.T.exists_borelPairs_universalFrame_openChart hS E H Dw l Xo c p A j y₀ π X s u hj hu, hc, hl, hc', hl'⟩

end GlobalTheory.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntFrExtOfGoodLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Exist

theorem exists_prime_mem_maximalIdeal_of_finite_residue (V : Type) [CommRing V] [IsLocalRing V]
    [Finite (IsLocalRing.ResidueField V)] : ∃ p : ℕ, p.Prime ∧ (p : V) ∈ IsLocalRing.maximalIdeal V := by
  obtain ⟨p, hp⟩ := CharP.exists (IsLocalRing.ResidueField V)
  refine ⟨p, CharP.char_is_prime (IsLocalRing.ResidueField V) p, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem intFrExt_of_good : PartI → N1ab → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → IntFrExt Xo c := by
  intro hP hN hB hT E _ _ _ H Dw l Xo c hpq hgood T io hfin x hx
  have : Finite (IsLocalRing.ResidueField T.V) := hfin
  obtain ⟨p, hp, hpm⟩ := exists_prime_mem_maximalIdeal_of_finite_residue T.V
  obtain ⟨O, _, β, Y, hPI, b, hb⟩ := GlobalTheory.T.exists_model_pushInvertible_over_completeDVR hP hN E H Dw l Xo c hpq T io p hp hpm (hgood p hp)
  have hIF := GlobalTheory.T.exists_integralFrames_model_invertible_pushforward hB hT E H Dw l Xo c
  let _ := io.toAlgebra
  obtain ⟨y₀, -, h0, -, -⟩ := gfp_frPt_gen (Xo := Xo) (c := c) (L := T.Fr) (L' := T.Fr) hT (fun _ => rfl) x hx
    (fun _ i j => if i = j then 1 else 0) (fun _ _ => if_pos rfl) (fun _ _ _ h => if_neg h.ne')
  obtain ⟨y, t, hbor⟩ := intFr_of_model hIF T io Y hPI b hb y₀
  refine ⟨T, RingHom.id _, 1, one_pos, fun z => by simp, hfin, y, ?_⟩
  have h1 : y.1.x = y₀.x := hbor.1
  have h2 : spMap (RingHom.id T.Fr) = 𝟙 _ := Spec.map_id _
  show y.1.x = _
  rw [h2, Category.id_comp, h1, h0]

end GlobalTheory.Exist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralLatticeStructureUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralLattice_structure_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), IntLatU Xo c := by
  first | exact @GlobalTheory.Frames.intLatU_holds | exact GlobalTheory.Frames.intLatU_holds | (intros; apply GlobalTheory.Frames.intLatU_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProperOfSubsingleton
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLocusOpen

theorem exists_sections {S : Scheme.{0}} (X T : Over S) [Etale X.hom] (n : ℕ) (x : Fin n → (T ⟶ X)) :
    ∃ (Z : Over S) (_ : Etale Z.hom) (z : T ⟶ Z) (σ : Fin n → (Z ⟶ X)), ∀ i, z ≫ σ i = x i := by
  induction n with
  | zero => exact ⟨𝟙_ _, inferInstanceAs (Etale (𝟙 S)), toUnit _, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨Z, hZ, z, σ, h⟩ := ih fun i => x i.succ
    refine ⟨Z ⊗ X, inferInstanceAs (Etale (pullback.fst Z.hom X.hom ≫ Z.hom)), lift z (x 0),
      Fin.cons (snd Z X) fun i => fst Z X ≫ σ i, fun i => ?_⟩
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · simp [h]

theorem comp_eq_iff {S : Scheme.{0}} {X Z : Over S} [Etale X.hom] [IsSeparated X.hom] (a b : Z ⟶ X)
    {K : Type} [Field K] {t : Sp K ⟶ S} (z : Over.mk t ⟶ Z) (p : Sp K) :
    z ≫ a = z ≫ b ↔ z.left p ∈ Set.range (equalizer.ι a b).left := by
  constructor
  · intro h
    refine ⟨(equalizer.lift z h).left p, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
  · rintro ⟨e, he⟩
    obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := z.left) (g := (equalizer.ι a b).left) p e he.symm
    have : Nonempty ↥(pullback z.left (equalizer.ι a b).left) := ⟨w⟩
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    have : PreconnectedSpace (Over.mk t).left := inferInstanceAs (PreconnectedSpace (Sp K))
    refine Over.OverMorphism.ext (eq_of_preconnected_of_unramified X.hom
      ((Over.w (z ≫ a)).trans (Over.w (z ≫ b)).symm) (pullback.fst z.left (equalizer.ι a b).left) ?_)
    rw [Over.comp_left, Over.comp_left, pullback.condition_assoc, pullback.condition_assoc, ← Over.comp_left,
      ← Over.comp_left, equalizer.condition]

theorem exists_open_injective {S : Scheme.{0}} (X : Over S) [Etale X.hom] [IsSeparated X.hom]
    {K : Type} [Field K] (t : Sp K ⟶ S) (p : Sp K) (n : ℕ) (x : Fin n → (Over.mk t ⟶ X))
    (hx : Function.Injective x) :
    ∃ U : Set S, IsOpen U ∧ t p ∈ U ∧ ∀ s ∈ U, ∃ (K' : Type) (_ : Field K') (_ : IsAlgClosed K') (t' : Sp K' ⟶ S),
      s ∈ Set.range t' ∧ ∃ x' : Fin n → (Over.mk t' ⟶ X), Function.Injective x' := by
  obtain ⟨Z, hZ, z, σ, h⟩ := exists_sections X (Over.mk t) n x
  let V : Set Z.left := ⋂ (i : Fin n) (j : Fin n) (_ : i ≠ j), (Set.range (equalizer.ι (σ i) (σ j)).left)ᶜ
  have hV : IsOpen V := isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    isOpen_iInter_of_finite fun _ => by
      have := isClosedImmersion_equalizer_ι_left (σ i) (σ j)
      exact (equalizer.ι (σ i) (σ j)).left.isClosedEmbedding.isClosed_range.isOpen_compl
  refine ⟨Z.hom '' V, Z.hom.isOpenMap V hV, ⟨z.left p, ?_, ?_⟩, ?_⟩
  · refine Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun j => Set.mem_iInter.2 fun hij hm => hij (hx ?_)
    rw [← h, ← h]
    exact (comp_eq_iff _ _ z p).2 hm
  · rw [← Scheme.Hom.comp_apply, Over.w]; rfl
  · rintro _ ⟨v, hv, rfl⟩
    let K' := AlgebraicClosure (Z.left.residueField v)
    let u : Sp K' ⟶ Z.left := spMap (algebraMap (Z.left.residueField v) K') ≫ Z.left.fromSpecResidueField v
    have q : Sp K' := (default : PrimeSpectrum K')
    have hu : u q = v := Scheme.fromSpecResidueField_apply v _
    let u' : Over.mk (u ≫ Z.hom) ⟶ Z := Over.homMk u rfl
    refine ⟨K', inferInstance, inferInstance, u ≫ Z.hom, ⟨q, congrArg (fun y => Z.hom y) hu⟩,
      fun i => u' ≫ σ i, fun i j hij => by_contra fun hne => ?_⟩
    have hm := (comp_eq_iff _ _ u' q).1 hij
    exact Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1 hv i) j) hne (hu ▸ hm)

theorem isProper_of_subsingleton {K : Type} [Field K] (G : Over (Sp K)) [GrpObj G] (T : TorusExtension G)
    (hT : Subsingleton T.X) : IsProper G.hom := by
  letI := T.addCommGroup
  letI := T.grpB
  have := T.q_hom
  have := T.i_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  have hp := T.isKernel
  have : Mono T.q := ⟨fun {Y} x y hxy => by
    have h1 : (x * y⁻¹) ≫ T.q = toUnit _ ≫ η[T.B] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
      rfl
    have h2 : hp.lift _ _ h1 = 1 := (GlobalTheory.splitTorusPointsEquiv (Sp K) T.X Y).injective (Subsingleton.elim _ _)
    have h3 := hp.lift_fst _ _ h1
    rw [h2, MonObj.one_comp] at h3
    exact mul_inv_eq_one.1 h3.symm⟩
  have : Mono T.q.left := inferInstanceAs (Mono ((Over.forget _).map T.q))
  have : EffectiveEpi T.q.left := inferInstance
  have : IsIso T.q.left := isIso_of_mono_of_strongEpi _
  have := T.isAbelian.proper
  rw [← Over.w T.q]
  infer_instance

theorem isProper_of_injective {k : Type} [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (hG : IsSemiAbelian G)
    (T : TorusExtension G) {g n : ℕ} (hg : SmoothOfRelativeDimension g G.hom) (h2 : 2 ≤ n) (hn : (n : k) ≠ 0)
    (x : Fin (n ^ (2 * g)) → {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ n = 1}) (hx : Function.Injective x) :
    IsProper G.hom := by
  letI := T.addCommGroup
  letI := T.grpB
  have := T.free
  have := T.finite
  have := T.i_hom
  have hc := card_torsion_mul_card_toric_torsion k G T g n hG hg hn
  have h0 : n ^ (2 * g) ≠ 0 := pow_ne_zero _ (by omega)
  have f₁ := Nat.finite_of_card_ne_zero (left_ne_zero_of_mul (hc ▸ h0))
  have f₂ := Nat.finite_of_card_ne_zero (right_ne_zero_of_mul (hc ▸ h0))
  have hle := Nat.card_le_card_of_injective x hx
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hle
  have hd : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ n = 1 ∧ ∃ y, x = y ≫ T.i} ≤ 1 :=
    Nat.le_of_mul_le_mul_left (by rw [hc, Nat.mul_one]; exact hle) (Nat.pos_of_ne_zero (left_ne_zero_of_mul (hc ▸ h0)))
  obtain ⟨e⟩ := SemiAbTorsionCount.nonempty_torus_points_mulEquiv k T.X
  have hcard := (SemiAbTorsionCount.divisible_and_card e n hn).2
  let i := IsMonHom.monoidHom T.i (𝟙_ (Over (Sp k)))
  have hi : Function.Injective i := fun a b h => T.isKernel.hom_ext h (toUnit_unique _ _)
  have h3 := Nat.card_le_card_of_injective
    (fun t : {t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) T.X // t ^ n = 1} =>
      (⟨i t.1, by rw [← map_pow, t.2, map_one], t.1, rfl⟩ :
        {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ n = 1 ∧ ∃ y, x = y ≫ T.i}))
    fun a b h => Subtype.ext (hi (congrArg Subtype.val h))
  rw [hcard] at h3
  have h4 : Module.finrank ℤ T.X = 0 := by
    by_contra hne
    exact absurd (h3.trans hd) (not_le.2 (Nat.one_lt_pow hne h2))
  exact isProper_of_subsingleton G T (Module.finrank_zero_iff.1 h4)

theorem nonempty_torsion_equiv {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) {K : Type} [Field K] (t : Sp K ⟶ S) :
    Nonempty ((Over.mk t ⟶ torsion G n) ≃ {x : 𝟙_ (Over (Sp K)) ⟶ (Over.pullback t).obj G // x ^ n = 1}) := by
  obtain ⟨e, -⟩ := exists_mulEquiv_of_isGrpPullback (isGrpPullback_pullback G t) (𝟙 _) t (Category.id_comp t).symm
  refine ⟨(TorsionUnram.torsionEquiv G n _).trans (e.toEquiv.subtypeEquiv fun x => ?_).symm⟩
  show x ^ n = 1 ↔ e x ^ n = 1
  rw [← map_pow, MulEquiv.map_eq_one_iff]

theorem isOpen_abLocus {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) {g n : ℕ}
    (hg : SmoothOfRelativeDimension g G.hom) (h2 : 2 ≤ n) (hn : IsUnit (n : Γ(S, ⊤))) : IsOpen (abLocus G) := by
  have := hG.comm
  have := hG.smooth
  have := hG.separated
  have := hG.geomConnected
  have := GrpTangent.etale_torsion G hn
  have hm : IsSeparated ((mulN G n).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have hm' : IsSeparated (mulN G n).left := IsSeparated.of_comp _ G.hom
  have : IsSeparated (torsion G n).hom :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (GrpTangent.isPullback_torsion G n) hm'
  have hK : ∀ (K : Type) [Field K] (t : Sp K ⟶ S), (n : K) ≠ 0 := fun K _ t => by
    have := ((hn.map t.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom).ne_zero
    simpa using this
  have hd : ∀ (K : Type) [Field K] (t : Sp K ⟶ S), SmoothOfRelativeDimension g ((Over.pullback t).obj G).hom :=
    fun K _ t => (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg
  refine isOpen_iff_forall_mem_open.2 fun s hs => ?_
  let K := AlgebraicClosure (S.residueField s)
  let t : Sp K ⟶ S := spMap (algebraMap (S.residueField s) K) ≫ S.fromSpecResidueField s
  have p : Sp K := (default : PrimeSpectrum K)
  have ht : t p = s := Scheme.fromSpecResidueField_apply s _
  have hB : IsAbelianScheme ((Over.pullback t).obj G) :=
    ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd _ _)), hs K t ⟨p, ht⟩,
      inferInstanceAs (GeometricallyConnected (pullback.snd _ _))⟩
  have hc := GlobalTheory.T.card_torsion_eq_pow_two_mul_dim K _ g n hB (hd K t) (hK K t)
  have := Nat.finite_of_card_ne_zero (hc ▸ pow_ne_zero _ (by omega : n ≠ 0))
  obtain ⟨e⟩ := nonempty_torsion_equiv G n t
  let x := ((Finite.equivFinOfCardEq hc).symm.trans e.symm)
  obtain ⟨U, hU, hp, h⟩ := exists_open_injective (torsion G n) t p _ x x.injective
  refine ⟨U, fun s' hs' => ?_, hU, ht ▸ hp⟩
  obtain ⟨K', _, _, t', hr, x', hx'⟩ := h s' hs'
  obtain ⟨e'⟩ := nonempty_torsion_equiv G n t'
  obtain ⟨T⟩ := hG.fibres K' t'
  exact abLocusOne S G hG K' t' (isProper_of_injective _ (IsSemiAbelian.pullback _ G hG) T (hd K' t') h2 (hK K' t')
    (e' ∘ x') (e'.injective.comp hx')) hr

theorem isOpen_abLocus_local {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]
    (hG : IsSemiAbelian G) : IsOpen (abLocus G) := by
  have := hG.smooth
  have := hG.geomConnected
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace G.hom G.hom.isOpenMap
  obtain ⟨x₀⟩ : Nonempty G.left := inferInstance
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected G.hom x₀
  obtain ⟨n, h2, hn⟩ : ∃ n : ℕ, 2 ≤ n ∧ IsUnit (n : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by exact_mod_cast h⟩
    · exact ⟨2, le_rfl, by exact_mod_cast (IsUnit.neg_iff _).1 h⟩
  exact isOpen_abLocus G hG hg h2 (by simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

end GlobalTheory.AbLocusOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianHomExtendsUniquelyOverDvr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem semiAbelian_hom_extends_uniquely_dvr :
    (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) :=
  existsUnique_hom_extension_semiAbelian_dvr AbelianSubgroupFinite.finite_of_torsionFree

end GlobalTheory
end

