import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0186
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0150

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelQuotientRepresentsReduced
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.LevelCover

noncomputable section

namespace GlobalTheory.LevelQuotRep

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem isSeparated_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R} (h : IsQProjOver f) :
    IsSeparated f := by
  obtain ⟨N, i, hi, -, rfl⟩ := h
  unfold PSpace.str
  infer_instance

theorem exists_lift_geom {W Z : Scheme.{0}} (q : W ⟶ Z) [LocallyOfFiniteType q] [Surjective q] {K : Type} [Field K]
    [IsAlgClosed K] (x : Sp K ⟶ Z) : ∃ h : Sp K ⟶ W, h ≫ q = x := by
  obtain ⟨y, -⟩ := (pullback.snd q x).surjective (IsLocalRing.closedPoint K)
  have : JacobsonSpace ↥(pullback q x) := LocallyOfFiniteType.jacobsonSpace (pullback.snd q x)
  obtain ⟨y', -, hy'⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback q x)))
    ⟨y, trivial⟩ isOpen_univ.isLocallyClosed
  have hc : IsClosed {y'} := hy'
  refine ⟨pointOfClosedPoint (pullback.snd q x) y' hc ≫ pullback.fst q x, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

theorem finite_etale_onto_spMap {K L : Type} [Field K] [Field L] [CharZero K] [CharZero L] [FiniteDimensional ℚ L]
    (k : K →+* L) : IsFinite (spMap k) ∧ Etale (spMap k) ∧ Surjective (spMap k) := by
  algebraize [k]
  have : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun x => by simp
  have hf : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  refine ⟨?_, ?_, ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩⟩
  · rw [IsFinite.SpecMap_iff]
    exact hf
  · rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
    have : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
    exact (⟨inferInstance, inferInstance⟩ : Algebra.Etale K L)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}

theorem finiteDimensional_KA (l : Level H) : FiniteDimensional ℚ (KA l) := by
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  rcases hx with rfl | rfl
  · refine IsIntegral.of_pow two_pos ?_
    rw [H.sqrt_neg_disc_sq]
    exact (isIntegral_algebraMap (x := (H.d : ℚ))).neg
  · refine IsIntegral.of_pow l.A_pos ?_
    rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
    exact isIntegral_one

section Obj

variable {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {b : Base l B} {b' : Base l B'} {b'' : Base l B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {o : Obj D l b s} {o' : Obj D l b' s'} {o'' : Obj D l b'' s''}

theorem obj_comp {f : S' ⟶ S} {f' : S'' ⟶ S'} (m' : ObjMap o'' o' f') (m : ObjMap o' o f) :
    Nonempty (ObjMap o'' o (f' ≫ f)) :=
  ⟨(((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o' o'').2 f f' m).1 m').choose⟩

theorem obj_cancel {f : S' ⟶ S} {e : S'' ⟶ S} (m : ObjMap o' o f) (n : ObjMap o'' o e) (g : S'' ⟶ S')
    (he : g ≫ f = e) : Nonempty (ObjMap o'' o' g) := by
  subst he
  exact ⟨(((ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o' o'').2 f g m).2 n).choose⟩

theorem obj_pull_same (o : Obj D l b s) (f : S' ⟶ S) : ∃ o' : Obj D l b (f ≫ s), Nonempty (ObjMap o' o f) :=
  obj_pull E H D l _ _ b b (RingHom.id _) _ _ s _ f rfl rfl (by rw [spMap_id', Category.comp_id]) o

end Obj

variable {Xo₂ : Moduli D l₂} (Q : LevelQuot l Xo₂)

theorem exists_lowers {B : Type} [CommRing B] {b : Base l B} {T : Scheme.{0}} {t : T ⟶ Sp B} {o : Obj D l b t}
    {z : T ⟶ Q.X} (n : ObjMap o Q.univ z) (y : T ⟶ Xo₂.X) (hy : y ≫ Q.π = z) :
    ∃ mu : SABMap o.t Xo₂.univ.t y, Lowers l Xo₂.univ o.eta o.etaA y mu.φ := by
  obtain ⟨mu, hmu⟩ := sab_cancel Q.m n.toSABMap y hy
  refine ⟨mu, fun a => sec_cancel mu Q.m _ _ ?_, fun a => sec_cancel mu Q.m _ _ ?_⟩
  · rw [hmu, Q.eta, ← Category.assoc, hy]; exact n.eta a
  · rw [hmu, Q.etaA, ← Category.assoc, hy]; exact n.etaA a

theorem hom_unique {B : Type} [CommRing B] {b : Base l B} {T : Scheme.{0}} [IsReduced T] {t : T ⟶ Sp B}
    {o : Obj D l b t} {f f' : T ⟶ Q.X} (h : f ≫ Q.s = f' ≫ Q.s) (m : ObjMap o Q.univ f) (m' : ObjMap o Q.univ f') :
    f = f' := by
  have := isSeparated_of_qproj Q.qproj
  have := Q.fin
  have := Q.onto
  refine (hom_eq_iff_forall_isAlgClosed Q.s h).mpr fun K _ _ x => ?_
  obtain ⟨ox, ⟨n⟩⟩ := obj_pull_same o x
  obtain ⟨u⟩ := obj_comp n m
  obtain ⟨u'⟩ := obj_comp n m'
  obtain ⟨y, hy⟩ := exists_lift_geom Q.π (x ≫ f)
  obtain ⟨y', hy'⟩ := exists_lift_geom Q.π (x ≫ f')
  obtain ⟨mu, hmu⟩ := exists_lowers Q u y hy
  obtain ⟨mu', hmu'⟩ := exists_lowers Q u' y' hy'
  rw [← hy, ← hy']
  refine Q.fibre K y y' ox.t mu mu' ox.eta ox.etaA ?_ hmu hmu'
  rw [← Q.overK, ← Category.assoc, ← Category.assoc, hy, hy', Category.assoc, Category.assoc, h]

def baseUp : Base l (KA l₂) where
  unit := (baseKA l₂).unit
  ρ := Q.jK (baseKA l).ρ
  ρ_sq := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  ζ := Q.jK (baseKA l).ζ
  ζ_prim := (baseKA l).ζ_prim.map_of_injective Q.jK.injective

theorem baseKA_rho_coe (l : Level H) : (((baseKA l).ρ : KA l) : ℂ) = H.rt0 := rfl

theorem baseUp_rho_coe : (((baseUp Q).ρ : KA l₂) : ℂ) = (((baseKA l).ρ : KA l) : ℂ) := Q.jK_val (baseKA l).ρ

theorem baseUp_rho : (baseUp Q).ρ = (baseKA l₂).ρ :=
  Subtype.ext ((baseUp_rho_coe Q).trans ((baseKA_rho_coe l).trans (baseKA_rho_coe l₂).symm))

theorem baseUp_zeta (hd : l.A ∣ l₂.A) : (baseUp Q).ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := Subtype.ext (by
  rw [IntermediateField.coe_pow]
  exact (Q.jK_val _).trans (zeta_dvd l₂.A_pos hd))

theorem exists_cover (hL : Out.Laws) (hpq : 1 ≤ D.p + D.q) (hd : l.Dvd l₂) {S : Scheme.{0}} [IsReduced S]
    {s' : S ⟶ Sp (KA l)} (ob : Obj D l (baseKA l) s') :
    ∃ (S₂ : Scheme.{0}) (q : S₂ ⟶ S) (g : S₂ ⟶ Q.X) (s₂ : S₂ ⟶ Sp (KA l₂)) (o : Obj D l (baseUp Q) s₂),
      IsFinite q ∧ Etale q ∧ Surjective q ∧ g ≫ Q.s = q ≫ s' ∧ Nonempty (ObjMap o ob q) ∧
        Nonempty (ObjMap o Q.univ g) := by
  have := finiteDimensional_KA l₂
  obtain ⟨k1, k2, k3⟩ := finite_etale_onto_spMap Q.jK
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseUp Q) Q.jK _ _ s' (pullback.snd s' (spMap Q.jK))
    (pullback.fst _ _) rfl rfl pullback.condition ob
  obtain ⟨S₂, p, o₂, m, hf, he, hs, ⟨hm₁, hm₂⟩, -⟩ := GlobalTheory.T.exists_finiteEtale_deeper_level_cover hL E H D l l₂ _ (baseUp Q) (baseKA l₂) _ _ o₁ hpq hd
    (baseUp_rho Q) (baseUp_zeta Q hd.2.2)
  have hr : IsReduced S₂ := isReduced_of_smooth_of_isReduced (p ≫ pullback.fst s' (spMap Q.jK))
  obtain ⟨f₂, ⟨hf₂, ⟨u⟩⟩, -⟩ := Xo₂.rep S₂ _ hr o₂
  let o := ObjLower.lower o₂ hd (baseUp_rho Q) (baseUp_zeta Q hd.2.2)
  let mo : ObjMap o o₁ p := ⟨m, hm₁, hm₂⟩
  obtain ⟨z, hz⟩ := sab_comp u.toSABMap Q.m rfl
  refine ⟨S₂, p ≫ pullback.fst _ _, f₂ ≫ Q.π, _, o, inferInstance, inferInstance, inferInstance, ?_,
    obj_comp mo n₁, ⟨⟨z, fun a => ?_, fun a => ?_⟩⟩⟩
  · rw [Category.assoc, Q.overK, ← Category.assoc, hf₂, Category.assoc, Category.assoc, pullback.condition]
  · show (o₂.eta a ^ (l₂.M / l.M)).left ≫ z.φ = _
    rw [hz, ← Category.assoc, sec_pow u.toSABMap _ _ (u.eta a), Category.assoc, Q.eta, Category.assoc]
  · show (o₂.etaA a ^ (l₂.A / l.A)).left ≫ z.φ = _
    rw [hz, ← Category.assoc, sec_pow u.toSABMap _ _ (u.etaA a), Category.assoc, Q.etaA, Category.assoc]

end GlobalTheory.LevelQuotRep

namespace GlobalTheory

open LevelQuotRep in

theorem levelQuot_represents : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (KA l)), IsReduced S → ∀ ob : Obj D l (baseKA l) s', ∃! f : S ⟶ Q.X, f ≫ Q.s = s' ∧ Nonempty (ObjMap ob Q.univ f) := by
  intro hL hL2 E _ _ _ H D l l₂ Xo₂ Q hpq hd S s' hS ob
  refine existsUnique_of_exists_of_unique ?_
    fun f f' ⟨h, ⟨m⟩⟩ ⟨h', ⟨m'⟩⟩ => hom_unique Q (h.trans h'.symm) m m'
  obtain ⟨S₂, q, g, s₂, o, hf, he, hs, hg, ⟨mq⟩, ⟨mg⟩⟩ := exists_cover Q hL hpq hd ob
  have key : pullback.fst q q ≫ g = pullback.snd q q ≫ g := by
    have : IsReduced (pullback q q) := isReduced_of_smooth_of_isReduced (pullback.fst q q ≫ q)
    obtain ⟨oR, ⟨n⟩⟩ := obj_pull_same o (pullback.fst q q)
    obtain ⟨n₁⟩ := obj_comp n mq
    obtain ⟨n'⟩ := obj_cancel mq n₁ (pullback.snd q q) pullback.condition.symm
    obtain ⟨u⟩ := obj_comp n mg
    obtain ⟨u'⟩ := obj_comp n' mg
    exact hom_unique Q (by rw [Category.assoc, Category.assoc, hg, pullback.condition_assoc]) u u'
  have hcoeq : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ S₂), g₁ ≫ q = g₂ ≫ q → g₁ ≫ g = g₂ ≫ g := fun g₁ g₂ h => by
    have := pullback.lift g₁ g₂ h ≫= key
    rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this
  have hfac : q ≫ EffectiveEpi.desc q g hcoeq = g := EffectiveEpi.fac q g hcoeq
  refine ⟨EffectiveEpi.desc q g hcoeq, ?_, ?_⟩
  · rw [← cancel_epi q, ← Category.assoc, hfac, hg]
  · exact GlobalTheory.T.nonempty_objMap_of_finite_etale_surjective_cover hL hL2 E H D l _ _ _ _ _ _ _ _ _ _ _ _ Q.univ ob o q _ (Or.inl hS) hf he hs ⟨mq⟩
      (hfac.symm ▸ ⟨mg⟩)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemRangeOfIsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.UnivProp

set_option backward.isDefEq.respectTransparency false

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ β : A →+* B, f = spMap β :=
  ⟨(Spec.preimage f).hom, by simp [spMap]⟩

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_geomPt (X : Scheme.{0}) (p : X) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (y : Sp K ⟶ X), p ∈ Set.range y := by
  refine ⟨AlgebraicClosure (X.residueField p), inferInstance, inferInstance,
    spMap (algebraMap (X.residueField p) _) ≫ X.fromSpecResidueField p, ⟨(default : PrimeSpectrum _), ?_⟩⟩
  rw [Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply p _

theorem exists_lift_field {X V : Scheme.{0}} (x : V ⟶ X) [IsOpenImmersion x] {K : Type} [Field K] (y : Sp K ⟶ X)
    {p : X} (hy : p ∈ Set.range y) (hx : p ∈ Set.range x) : ∃ z : Sp K ⟶ V, z ≫ x = y := by
  have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  refine ⟨IsOpenImmersion.lift x y ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨a, rfl⟩
  obtain ⟨a', rfl⟩ := hy
  rwa [Subsingleton.elim a a']

theorem hom_ext_affine {X Y : Scheme.{0}} (f g : X ⟶ Y)
    (h : ∀ p : X, ∃ (V : Scheme.{0}) (x : V ⟶ X), IsOpenImmersion x ∧ p ∈ Set.range x ∧ x ≫ f = x ≫ g) : f = g := by
  refine Scheme.hom_ext_of_forall f g fun p => ?_
  obtain ⟨V, x, hx, hp, e⟩ := h p
  refine ⟨x.opensRange, hp, ?_⟩
  rw [← x.isoOpensRange_inv_comp, Category.assoc, Category.assoc, e]

theorem exists_glue {X Y : Scheme.{0}} {I : Type} (V : I → Scheme.{0}) (x : ∀ i, V i ⟶ X) (hx : ∀ i, IsOpenImmersion (x i))
    (hc : ∀ p : X, ∃ i, p ∈ Set.range (x i)) (f : ∀ i, V i ⟶ Y)
    (h : ∀ i j (T : Type) [CommRing T] (z : Sp T ⟶ V i) (z' : Sp T ⟶ V j), z ≫ x i = z' ≫ x j → z ≫ f i = z' ≫ f j) :
    ∃ F : X ⟶ Y, ∀ i, x i ≫ F = f i := by
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers I V x hc hx
  refine ⟨Scheme.Cover.glueMorphisms 𝒰 f fun i j => ?_, fun i => Scheme.Cover.ι_glueMorphisms 𝒰 f _ i⟩
  refine hom_ext_affine _ _ fun p => ?_
  obtain ⟨W, hW, hp, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := p) trivial
  refine ⟨_, hW.fromSpec, inferInstance, by rw [hW.range_fromSpec]; exact hp, ?_⟩
  have := h i j Γ(pullback (x i) (x j), W) (hW.fromSpec ≫ pullback.fst (x i) (x j)) (hW.fromSpec ≫ pullback.snd (x i) (x j))
    (by rw [Category.assoc, Category.assoc, pullback.condition])
  rw [Category.assoc, Category.assoc] at this
  exact this

theorem exists_glue' {X Y : Scheme.{0}} {I : Type} (V : I → Scheme.{0}) (x : ∀ i, V i ⟶ X) (hx : ∀ i, IsOpenImmersion (x i))
    (hc : ∀ p : X, ∃ i, p ∈ Set.range (x i)) (f : ∀ i, V i ⟶ Y)
    (h : ∀ i j (p : X), p ∈ Set.range (x i) → p ∈ Set.range (x j) → ∃ (k : I) (c : V k ⟶ V i) (c' : V k ⟶ V j),
      p ∈ Set.range (x k) ∧ c ≫ x i = x k ∧ c' ≫ x j = x k ∧ c ≫ f i = c' ≫ f j) :
    ∃ F : X ⟶ Y, ∀ i, x i ≫ F = f i := by
  refine exists_glue V x hx hc f fun i j T _ z z' e => hom_ext_affine _ _ fun p => ?_
  obtain ⟨k, c, c', hp, e₁, e₂, e₃⟩ := h i j ((z ≫ x i) p) ⟨z p, by simp⟩ (by rw [e]; exact ⟨z' p, by simp⟩)
  have := hx i
  have := hx j
  have := hx k
  refine ⟨_, pullback.fst (z ≫ x i) (x k), inferInstance, by rw [Scheme.Pullback.range_fst]; exact hp, ?_⟩
  have a₁ : pullback.fst (z ≫ x i) (x k) ≫ z = pullback.snd (z ≫ x i) (x k) ≫ c := by
    rw [← cancel_mono (x i), Category.assoc, Category.assoc, e₁, pullback.condition]
  have a₂ : pullback.fst (z ≫ x i) (x k) ≫ z' = pullback.snd (z ≫ x i) (x k) ≫ c' := by
    rw [← cancel_mono (x j), Category.assoc, Category.assoc, e₂, ← e, pullback.condition]
  rw [← Category.assoc, ← Category.assoc, a₁, a₂, Category.assoc, Category.assoc, e₃]

variable {o : Type} [CommRing o] {g : ℕ} {J : Type}

def TBy {k : ℕ} {b : TBase o k} {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} (t' : TObj g k J b s')
    (t : TObj g k J b s) (f : S' ⟶ S) (φ : t'.A.left ⟶ t.A.left) : Prop :=
  IsGrpPullback t'.A t.A f φ ∧ LBIso t'.L (t.L.pull φ) ∧
    (∀ i, (t'.pt i).left ≫ φ = f ≫ (t.pt i).left) ∧ ∀ j, (t'.act j).left ≫ φ = φ ≫ (t.act j).left

theorem TBy.comp {k : ℕ} {b : TBase o k} {S S' S'' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o}
    {t : TObj g k J b s} {t' : TObj g k J b s'} {t'' : TObj g k J b s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {φ} {φ'}
    (h' : TBy t'' t' f' φ') (h : TBy t' t f φ) : TBy t'' t (f' ≫ f) (φ' ≫ φ) := by
  refine ⟨h'.1.comp h.1, LBIso.trans t''.isLB (pull_isLB t'.isLB _) (pull_isLB t.isLB _) h'.2.1
    (GlobalTheory.GenSpread.lbIso_pull_of_lbIso h.2.1 φ' rfl), fun i => ?_, fun j => ?_⟩
  · rw [← Category.assoc, h'.2.2.1, Category.assoc, h.2.2.1, Category.assoc]
  · rw [← Category.assoc, h'.2.2.2, Category.assoc, h.2.2.2, Category.assoc]

variable {N' : ℕ} {b : TBase o (N' ^ 2)} {m : ℕ}

theorem TBy.unique (hL : Out.Laws) (hL2 : Out.Laws2) (hm : 2 ≤ m) (hd : m ^ 2 ∣ N') (ho : Odd N')
    {R : Type} [CommRing R] [_root_.IsReduced R] {β : o →+* R} {S : Scheme.{0}} {s : S ⟶ Sp o}
    {t : TObj g (N' ^ 2) J b s} {u : TObj g (N' ^ 2) J b (spMap β)} {x : Sp R ⟶ S} {φ φ'}
    (h : TBy u t x φ) (h' : TBy u t x φ') : φ = φ' := by
  obtain ⟨e, he, e₁⟩ := grpPullback_iso h'.1 h.1
  have : IsMonHom (Iso.refl u.A).hom := inferInstanceAs (IsMonHom (𝟙 u.A))
  have hd := (GlobalTheory.T.thetaLevel_iso_unique_of_dense_common_fibres hL hL2 o g N' J b m R β u u hm hd ho (fun p => subset_closure (by
    obtain ⟨K, _, _, y, hy⟩ := exists_geomPt _ p
    obtain ⟨w, hw⟩ := GlobalTheory.tObj_pull o g _ J b _ _ (spMap β) _ y u rfl
    exact ⟨K, inferInstance, y, w, hy, hw, hw⟩))).2 e.hom.left (Iso.refl u.A).hom.left
    (isGrpPullback_of_iso e) (isGrpPullback_of_iso (Iso.refl u.A))
    (LBIso.trans u.isLB (pull_isLB t.isLB _) (pull_isLB u.isLB _) h'.2.1
      (GlobalTheory.GenSpread.lbIso_pull_of_lbIso h.2.1 _ e₁.symm).symm)
    (LBIso.trans u.isLB (pull_isLB t.isLB _) (pull_isLB u.isLB _) h.2.1
      (GlobalTheory.GenSpread.lbIso_pull_of_lbIso h.2.1 _ (by simp)).symm) (fun i => by
      apply h.1.1.hom_ext
      · rw [Category.assoc, e₁, h'.2.2.1]
        simpa using (h.2.2.1 i).symm
      · simp)
  rw [← e₁, hd]
  simp

theorem exists_common (hL : Out.Laws) (hL2 : Out.Laws2) (hm : 2 ≤ m) (hd : m ^ 2 ∣ N') (ho : Odd N')
    {S : Scheme.{0}} {s : S ⟶ Sp o} {t t' : TObj g (N' ^ 2) J b s}
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S) (u : TObj g (N' ^ 2) J b (y ≫ s)), TMap u t y → TMap u t' y)
    {R : Type} [CommRing R] [_root_.IsReduced R] (x : Sp R ⟶ S) (β : o →+* R) (hβ : x ≫ s = spMap β) :
    ∃ (u : TObj g (N' ^ 2) J b (spMap β)) (a : _) (φ : _), TBy u t x a ∧ TBy u t' x φ := by
  obtain ⟨u, a, ha⟩ := GlobalTheory.tObj_pull o g _ J b _ _ s _ x t hβ
  obtain ⟨u', hu'⟩ := GlobalTheory.tObj_pull o g _ J b _ _ s _ x t' hβ
  have h' : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S) (sy : Sp K ⟶ Sp o) (u : TObj g (N' ^ 2) J b sy),
      y ≫ s = sy → TMap u t y → TMap u t' y := by
    intro K _ _ y sy u e
    subst e
    exact h K y u
  have h₁ : TMap u u' (𝟙 _) := (GlobalTheory.T.thetaLevel_iso_unique_of_dense_common_fibres hL hL2 o g N' J b m R β u u' hm hd ho (fun p => subset_closure (by
    obtain ⟨K, _, _, y, hy⟩ := exists_geomPt _ p
    obtain ⟨w, hw⟩ := GlobalTheory.tObj_pull o g _ J b _ _ (spMap β) _ y u rfl
    refine ⟨K, inferInstance, y, w, hy, hw, ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ t' u' w).2 x y hu').2 ?_⟩
    exact h' K _ _ w (by rw [Category.assoc, hβ])
      (((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ t u w).2 x y ⟨a, ha⟩).1 hw)))).1
  have h₂ := ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ t' u' u).2 x _ hu').1 h₁
  rw [Category.id_comp] at h₂
  obtain ⟨φ, hφ⟩ := h₂
  exact ⟨u, a, φ, ha, hφ⟩

theorem mem_range_of_isPullback {P X Y Z : Scheme.{0}} {a : P ⟶ X} {q : P ⟶ Y} {f : X ⟶ Z} {x : Y ⟶ Z}
    (h : IsPullback a q f x) (p : X) : p ∈ Set.range a ↔ f p ∈ Set.range x := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨q z, by rw [← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback h p y hy.symm
    exact ⟨z, hz⟩

theorem tMap_id_of_geomPt (hL : Out.Laws) (hL2 : Out.Laws2) (hm : 2 ≤ m) (hd : m ^ 2 ∣ N') (ho : Odd N')
    {S : Scheme.{0}} [IsReduced S] {s : S ⟶ Sp o} {t t' : TObj g (N' ^ 2) J b s}
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S) (u : TObj g (N' ^ 2) J b (y ≫ s)), TMap u t y → TMap u t' y) :
    TMap t t' (𝟙 S) := by
  let x : ∀ V : S.affineOpens, Sp Γ(S, V) ⟶ S := fun V => V.2.fromSpec
  have hx : ∀ V, IsOpenImmersion (x V) := fun V => inferInstanceAs (IsOpenImmersion V.2.fromSpec)
  have rx : ∀ V, Set.range (x V) = V.1 := fun V => V.2.range_fromSpec
  choose β hβ using fun V => exists_spMap (x V ≫ s)
  choose u a φ ha hφ using fun V => exists_common hL hL2 hm hd ho h (x V) (β V) (hβ V)
  have cov : ∀ p : S, ∃ V, p ∈ Set.range (x V) := fun p => by
    obtain ⟨W, hW, hp, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := p) trivial
    exact ⟨⟨W, hW⟩, by rw [rx]; exact hp⟩
  have res : ∀ V W : S.affineOpens, W.1 ≤ V.1 → ∃ c : (u W).A.left ⟶ (u V).A.left, c ≫ a V = a W ∧ c ≫ φ V = φ W := by
    intro V W hle
    have := hx V
    have e := IsOpenImmersion.lift_fac (x V) (x W) (by rw [rx, rx]; exact hle)
    obtain ⟨c, hc⟩ := ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ t (u V) (u W)).2 (x V) _ ⟨_, ha V⟩).2
      (by rw [e]; exact ⟨_, ha W⟩)
    have h₁ := TBy.comp hc (ha V)
    have h₂ := TBy.comp hc (hφ V)
    rw [e] at h₁ h₂
    exact ⟨c, h₁.unique hL hL2 hm hd ho (ha W), h₂.unique hL hL2 hm hd ho (hφ W)⟩
  have ref : ∀ (V V' : S.affineOpens) (p : S), p ∈ Set.range (x V) → p ∈ Set.range (x V') →
      ∃ (W : S.affineOpens) (c : (u W).A.left ⟶ (u V).A.left) (c' : (u W).A.left ⟶ (u V').A.left),
        p ∈ Set.range (x W) ∧ c ≫ a V = a W ∧ c ≫ φ V = φ W ∧ c' ≫ a V' = a W ∧ c' ≫ φ V' = φ W := by
    intro V V' p hp hp'
    rw [rx] at hp hp'
    obtain ⟨W, hW, hpW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := V.1 ⊓ V'.1) (x := p) ⟨hp, hp'⟩
    obtain ⟨c, e₁, e₂⟩ := res V ⟨W, hW⟩ fun z hz => (hle hz).1
    obtain ⟨c', e₁', e₂'⟩ := res V' ⟨W, hW⟩ fun z hz => (hle hz).2
    exact ⟨⟨W, hW⟩, c, c', by rw [rx]; exact hpW, e₁, e₂, e₁', e₂'⟩
  have oa : ∀ V, IsOpenImmersion (a V) := fun V => MorphismProperty.of_isPullback (ha V).1.1.flip (hx V)
  have oφ : ∀ V, IsOpenImmersion (φ V) := fun V => MorphismProperty.of_isPullback (hφ V).1.1.flip (hx V)
  have ca : ∀ p : t.A.left, ∃ V, p ∈ Set.range (a V) := fun p => by
    obtain ⟨V, hV⟩ := cov (t.A.hom p)
    exact ⟨V, (mem_range_of_isPullback (ha V).1.1 p).2 hV⟩
  have cφ : ∀ p : t'.A.left, ∃ V, p ∈ Set.range (φ V) := fun p => by
    obtain ⟨V, hV⟩ := cov (t'.A.hom p)
    exact ⟨V, (mem_range_of_isPullback (hφ V).1.1 p).2 hV⟩
  obtain ⟨Φ, hΦ⟩ := exists_glue' _ a oa ca φ fun V V' p hp hp' => by
    obtain ⟨W, c, c', hW, e₁, e₂, e₃, e₄⟩ := ref V V' _ ((mem_range_of_isPullback (ha V).1.1 p).1 hp)
      ((mem_range_of_isPullback (ha V').1.1 p).1 hp')
    exact ⟨W, c, c', (mem_range_of_isPullback (ha W).1.1 p).2 hW, e₁, e₃, e₂.trans e₄.symm⟩
  obtain ⟨Ψ, hΨ⟩ := exists_glue' _ φ oφ cφ a fun V V' p hp hp' => by
    obtain ⟨W, c, c', hW, e₁, e₂, e₃, e₄⟩ := ref V V' _ ((mem_range_of_isPullback (hφ V).1.1 p).1 hp)
      ((mem_range_of_isPullback (hφ V').1.1 p).1 hp')
    exact ⟨W, c, c', (mem_range_of_isPullback (hφ W).1.1 p).2 hW, e₂, e₄, e₁.trans e₃.symm⟩
  have exta : ∀ {Y : Scheme.{0}} (f f' : t.A.left ⟶ Y), (∀ V, a V ≫ f = a V ≫ f') → f = f' := fun f f' e =>
    hom_ext_affine f f' fun p => by
      obtain ⟨V, hV⟩ := ca p
      exact ⟨_, a V, oa V, hV, e V⟩
  have iso : IsIso Φ := ⟨Ψ, exta _ _ fun V => by rw [← Category.assoc, hΦ, hΨ, Category.comp_id],
    hom_ext_affine _ _ fun p => by
      obtain ⟨V, hV⟩ := cφ p
      exact ⟨_, φ V, oφ V, hV, by rw [← Category.assoc, hΨ, hΦ, Category.comp_id]⟩⟩
  have grp : IsGrpPullback t.A t'.A (𝟙 S) Φ := GlobalTheory.GrpLoc.isGrpPullback_local_on_base S t.A t'.A Φ iso
    (exta _ _ fun V => by rw [← Category.assoc, hΦ, (hφ V).1.1.w, (ha V).1.1.w]) fun p => by
      obtain ⟨V, hV⟩ := cov p
      exact ⟨_, x V, (u V).A, inferInstance, a V, hx V, hV, (ha V).1, by rw [hΦ]; exact (hφ V).1⟩
  refine ⟨Φ, grp, GlobalTheory.RigidLocal.lbIso_of_local hL.globalFns S t.A t'.A t.L t'.L Φ t.ab t.isLB t'.isLB t.rigid t'.rigid grp fun p => ?_,
    fun i => hom_ext_affine _ _ fun p => ?_, fun j => exta _ _ fun V => ?_⟩
  · obtain ⟨V, hV⟩ := cov p
    refine ⟨_, _, x V, (u V).A.hom, a V, hx V, hV, (ha V).1.1, ?_⟩
    rw [hΦ]
    exact LBIso.trans (pull_isLB t.isLB _) (u V).isLB (pull_isLB t'.isLB _) (ha V).2.1.symm (hφ V).2.1
  · obtain ⟨V, hV⟩ := cov p
    refine ⟨_, x V, hx V, hV, ?_⟩
    rw [← Category.assoc, ← (ha V).2.2.1, Category.assoc, hΦ, (hφ V).2.2.1, Category.id_comp]
  · rw [← Category.assoc, ← (ha V).2.2.2, Category.assoc, hΦ, (hφ V).2.2.2, ← Category.assoc, hΦ]

end GlobalTheory.ZM.UnivProp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationExtendsOverDvrGoodReduction
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.PolExtendDVR

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB Y} {M : LB X} {φ : Y ⟶ X} (h : LBIso L (M.pull φ)) (g : Z ⟶ Y) :
    LBIso (L.pull g) (M.pull (g ≫ φ)) :=
  LBIso.chartPull (Geo.Tor.chartPullPull L g g rfl)
    (chartPullSame M (fun _ : PUnit => g ≫ φ) (fun _ => φ) (fun _ => 1) g fun _ => rfl) h

theorem exists_baseChange (hB : PolBaseChangeSt) {V K V' K' : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K]
    [IsFractionRing V K] [CommRing V'] [IsDomain V'] [Field K'] [Algebra V' K'] [IsFractionRing V' K']
    (a : V →+* V') (ha : Function.Injective a)
    (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left)
    (hφ : IsGrpPullback P.A B (spMap (algebraMap V K)) φ) (hL : LBIso P.L (M.L.L.pull φ)) :
    ∃ (P' : PolAV (Sp K')) (M' : GlobalTheory.UU.CP ((Over.pullback (spMap a)).obj B))
      (φ' : P'.A.left ⟶ ((Over.pullback (spMap a)).obj B).left),
      IsGrpPullback P'.A ((Over.pullback (spMap a)).obj B) (spMap (algebraMap V' K')) φ' ∧
        LBIso P'.L (M'.L.L.pull φ') ∧ LBIso M'.L.L (M.L.L.pull (pullback.fst B.hom (spMap a))) := by
  have hi : Function.Injective ((algebraMap V' K').comp a) := (IsFractionRing.injective V' K').comp ha
  let b : K →+* K' := IsFractionRing.lift hi
  have hb : b.comp (algebraMap V K) = (algebraMap V' K').comp a :=
    RingHom.ext fun x => IsFractionRing.lift_algebraMap hi x
  have hs : spMap b ≫ spMap (algebraMap V K) = spMap (algebraMap V' K') ≫ spMap a := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hb]
  obtain ⟨P', g, hg, -, hm, t, ht⟩ := hB _ _ (spMap b) P
  have gp : IsGrpPullback P'.A P.A (spMap b) g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = toBase hg.w y), ← hm]
    rfl⟩
  have hπ := isGrpPullback_pullback B (spMap a)
  have gc := (gp.comp hφ).congr hs rfl
  obtain ⟨M', w, hw⟩ := GlobalTheory.UU.exists_pull M (GlobalTheory.UU.toBase_mul_pullback B (spMap a))
  have hM : LBIso M'.L.L (M.L.L.pull (pullback.fst B.hom (spMap a))) := ⟨w, hw.gen⟩
  let φ' : P'.A.left ⟶ ((Over.pullback (spMap a)).obj B).left :=
    pullback.lift (g ≫ φ) (P'.A.hom ≫ spMap (algebraMap V' K')) (gc.1.w.trans (Category.assoc _ _ _).symm)
  have e : φ' ≫ pullback.fst B.hom (spMap a) = g ≫ φ := pullback.lift_fst _ _ _
  refine ⟨P', M', φ', hπ.cancel (gc.congr rfl e.symm) (pullback.lift_snd _ _ _), ?_, hM⟩
  have i₁ : LBIso P'.L (M.L.L.pull (g ≫ φ)) :=
    LBIso.trans P'.isLB (pull_isLB P.isLB _) (pull_isLB M.L.isLB _) (LBIso.symm ⟨t, ht⟩) (lbIso_pull_comp hL g)
  have i₂ := lbIso_pull_comp hM φ'
  rw [e] at i₂
  exact LBIso.trans P'.isLB (pull_isLB M.L.isLB _) (pull_isLB M'.L.isLB _) i₁ i₂.symm

end GlobalTheory.PolExtendDVR

namespace GlobalTheory

open PolExtendDVR IsLocalRing in

theorem polarisation_extends_dvr : Laws → Laws2 → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → RelAmple B M.L.L ∧ KTriv B M.L.L := by
  intro h h₂ V K _ _ _ _ _ _ P B _ _ M φ hB hφ hL
  let V' := AdicCompletion (maximalIdeal V) V
  obtain ⟨P', M', φ', hφ', hL', hM⟩ := exists_baseChange (K' := FractionRing V') h.polBaseChange (algebraMap V V')
    (algebraMap_adicCompletion_injective_of_dvr V) P B M φ hφ hL
  have hπ := isGrpPullback_pullback B (spMap (algebraMap V V'))
  have hB' := PolPull.isAbelianScheme_of_isGrpPullback hB hπ
  have hA' := GlobalTheory.T.relAmple_extended_principalPolarisation_dvr h h₂ V' (FractionRing V') P' _ M' φ' hB' hφ' hL' inferInstance
  have : Module.FaithfullyFlat V V' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hA : RelAmple B M.L.L :=
    AmpleDescent.relAmple_of_faithfullyFlat V V' B _ _ M.L.L M'.L.L hB hπ M.L.isLB M'.L.isLB hM hA'
  exact ⟨hA, KTrivSpread.kTriv_of_generic_fibre h V K P B M φ hB hφ hL hA⟩

end GlobalTheory
end
end

