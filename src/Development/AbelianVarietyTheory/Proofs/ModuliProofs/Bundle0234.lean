import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0232
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0222
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBigThetaSysWithAction
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0146
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalModelThetaTupleMaximalMinors
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0233
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelSchemeUniversalReducedBases
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem range_subset_iff_of_charts {X Hk S S₁ S₂ U G₀ G G₁ G₂ P : Scheme.{0}} {g₀ : G₀ ⟶ Hk} {gU : U ⟶ X}
    {m₁ : G₀ ⟶ U} {f : S ⟶ X} {g : G ⟶ S} {mu : G ⟶ U} (hmu : IsPullback mu g gU f)
    {K : Set G₀} {K' : Set G}
    {q₁ : S₁ ⟶ S} {g₁ : G₁ ⟶ S₁} {a₁ : G₁ ⟶ G} (ha₁ : a₁ ≫ g = g₁ ≫ q₁) {h₁ : S₁ ⟶ Hk} {n₁ : G₁ ⟶ G₀}
    (hn₁ : IsPullback n₁ g₁ g₀ h₁) (e₁ : n₁ ≫ m₁ = a₁ ≫ mu) (k₁ : a₁ ⁻¹' K' = n₁ ⁻¹' K)
    {q₂ : S₂ ⟶ S} {g₂ : G₂ ⟶ S₂} {a₂ : G₂ ⟶ G} (ha₂ : a₂ ≫ g = g₂ ≫ q₂) {h₂ : S₂ ⟶ Hk} {n₂ : G₂ ⟶ G₀}
    (hn₂ : IsPullback n₂ g₂ g₀ h₂) (e₂ : n₂ ≫ m₁ = a₂ ≫ mu) (k₂ : a₂ ⁻¹' K' = n₂ ⁻¹' K)
    (x₁ : P ⟶ S₁) (x₂ : P ⟶ S₂) (hx : x₁ ≫ q₁ = x₂ ≫ q₂)
    (u₁ u₂ : P ⟶ G₀) (hu₁ : u₁ ≫ g₀ = x₁ ≫ h₁) (hu₂ : u₂ ≫ g₀ = x₂ ≫ h₂) (hu : u₁ ≫ m₁ = u₂ ≫ m₁) :
    (Set.range u₁ ⊆ K ↔ Set.range u₂ ⊆ K) := by
  have key : ∀ {A B : Scheme.{0}} (w : P ⟶ A) (c : A ⟶ B) (L : Set B),
      Set.range (w ≫ c) ⊆ L ↔ Set.range w ⊆ c ⁻¹' L := by
    intro A B w c L
    simp [Set.range_subset_iff]
  obtain ⟨w₁, hw₁, hw₁'⟩ := hn₁.exists_lift u₁ x₁ hu₁
  obtain ⟨w₂, hw₂, hw₂'⟩ := hn₂.exists_lift u₂ x₂ hu₂
  have hw : w₁ ≫ a₁ = w₂ ≫ a₂ := by
    apply hmu.hom_ext
    · rw [Category.assoc, Category.assoc, ← e₁, ← e₂, ← Category.assoc, ← Category.assoc, hw₁, hw₂, hu]
    · rw [Category.assoc, Category.assoc, ha₁, ha₂, ← Category.assoc, ← Category.assoc, hw₁', hw₂', hx]
  rw [← hw₁, ← hw₂, key, key, ← k₁, ← k₂, ← key, ← key, hw]

theorem exists_kerScheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), admitted l 𝔓 p → ∃ Z : KerScheme Xo 𝔓 p i, EtSet Z.o₁.t.G Z.K := by
  intro E _ _ _ H D l Xo 𝔓 p i hA
  have laws : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨Hk, π₁, o₁, m₁, K, fin₁, et₁, hK, hE, hpt, hex⟩ := GlobalTheory.T.exists_heckeKernel_scheme_universal E H D l Xo 𝔓 p i hA
  refine ⟨⟨Hk, π₁, fin₁, et₁, o₁, m₁, K, hK, hE, ?_⟩, hE⟩
  intro S s hS o K' hE' hK'
  obtain ⟨f, ⟨hf, ⟨mu⟩⟩, hfu⟩ := Xo.rep S s hS o
  obtain ⟨S', π, o', m, τ, hπ₁, hπ₂, hπ₃, hL⟩ := GlobalTheory.T.hecke_set_etale_level_structure_exists E H D l 𝔓 p i S s o K' hA hE' hK'
  have hK'' := ((GlobalTheory.heckeSets_pull E H D 𝔓 p i S S' o.t o'.t π m.toSABMap o.proper).2 K').1 hK'
  obtain ⟨mu', hmu'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o o').2 f π mu).1 m
  obtain ⟨h', n', hh', hn', hKn'⟩ := hex S' (π ≫ s) o' (π ≫ f) mu' τ _ hL hK''
  have cm := m.cart.1
  have cm₁ := m₁.cart.1
  have cn' := n'.cart.1
  haveI : IsReduced S' := GlobalTheory.isReduced_of_smooth_of_isReduced π
  haveI : IsReduced (pullback π π : Scheme.{0}) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst π π)
  have hd : pullback.fst π π ≫ h' = pullback.snd π π ≫ h' := by
    have h0 : (pullback.fst π π ≫ h') ≫ π₁ = (pullback.snd π π ≫ h') ≫ π₁ := by
      rw [Category.assoc, Category.assoc, hh', pullback.condition_assoc]
    refine hom_ext_of_geometric_points _ _ _ π₁ _ _ h0 ?_
    intro k _ _ x
    refine hpt k _ _ (by rw [Category.assoc, Category.assoc x, h0]) ?_
    intro u u' huu
    exact range_subset_iff_of_charts mu.cart.1 cm.w cn' (hn'.trans hmu') hKn' cm.w cn' (hn'.trans hmu') hKn'
      (x ≫ pullback.fst π π) (x ≫ pullback.snd π π) (by rw [Category.assoc, Category.assoc, pullback.condition])
      u.left u'.left (by rw [Category.assoc]; exact Over.w u) (by rw [Category.assoc]; exact Over.w u') huu
  obtain ⟨h, hh⟩ : ∃ h : S ⟶ Hk, π ≫ h = h' := by
    suffices hc : ∀ {Z : Scheme.{0}} (a b : Z ⟶ S'), a ≫ π = b ≫ π → a ≫ h' = b ≫ h' from
      ⟨EffectiveEpi.desc π h' hc, EffectiveEpi.fac π h' hc⟩
    focus
      intro Z a b hab
      have := congrArg (pullback.lift a b hab ≫ ·) hd
      simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this
  have hhf : h ≫ π₁ = f := by
    rw [← cancel_epi π, ← Category.assoc, hh, hh']
  subst hhf
  obtain ⟨n, hn⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₁ o).2 π₁ h m₁).2 mu
  have cn := n.cart.1
  have hmn : m.toSABMap.φ ≫ n.toSABMap.φ = n'.toSABMap.φ := by
    apply cm₁.hom_ext
    · rw [Category.assoc, ← hn]
      exact (hn'.trans hmu').symm
    · rw [Category.assoc, cn.w, cn'.w, ← Category.assoc, cm.w, Category.assoc, hh]
  have hsurj : Surjective m.toSABMap.φ := MorphismProperty.of_isPullback cm.flip hπ₃
  have hKn : K' = n.toSABMap.φ ⁻¹' K := by
    apply hsurj.surj.preimage_injective
    rw [hKn', ← hmn]
    ext y
    simp
  refine ⟨h, ⟨by rw [← Category.assoc, hf], n, hKn⟩, ?_⟩
  rintro h₂ ⟨hs₂, n₂, hKn₂⟩
  obtain ⟨mu₂, hmu₂⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₁ o).2 π₁ h₂ m₁).1 n₂
  have h0 : h₂ ≫ π₁ = h ≫ π₁ := hfu _ ⟨by rw [Category.assoc, hs₂], ⟨mu₂⟩⟩
  have hrig : ∀ (f₂ : S ⟶ Xo.X) (mu₂ : ObjMap o Xo.univ f₂), f₂ = h ≫ π₁ → mu₂.toSABMap.φ = mu.toSABMap.φ := by
    intro f₂ mu₂ e
    subst e
    exact GlobalTheory.obj_rigid_closed laws E H D l _ _ _ _ _ _ _ _ Xo.univ o _ (Or.inl hS) _ _
      fun a => ⟨_, mu₂.eta a, mu.eta a⟩
  have e₂ := hmu₂.symm.trans (hrig _ mu₂ h0)
  refine hom_ext_of_geometric_points _ _ _ π₁ _ _ h0 ?_
  intro k _ _ x
  refine hpt k _ _ (by rw [Category.assoc, Category.assoc x, h0]) ?_
  intro u u' huu
  exact range_subset_iff_of_charts (q₁ := 𝟙 S) (q₂ := 𝟙 S) (a₁ := 𝟙 _) (a₂ := 𝟙 _) (K' := K') mu.cart.1 (by simp) n₂.cart.1
    (by rw [Category.id_comp]; exact e₂) (by rw [← hKn₂]; simp) (by simp) cn (by rw [Category.id_comp]; exact hn.symm)
    (by rw [← hKn]; simp) x x rfl u.left u'.left (Over.w u) (Over.w u') huu

end GlobalTheory.HkFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsTorsMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.FlatTors.TorsMapExists

open ReciprocityTheory.ChartRestriction.G.DVR

theorem isPull_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' T'' : Over (Sp R)}
    {a : T'.left ⟶ T.left} {b : T''.left ⟶ T'.left} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPt D T''}
    (h : GtPt.IsPull a g g') (h' : GtPt.IsPull b g' g'') : GtPt.IsPull (b ≫ a) g g'' := by
  refine ⟨by rw [h'.1, h.1, Category.assoc], fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  rw [val_corr hJ (h'.2 χ), val_pull hJ, val_corr hJ (h.2 χ), val_pull hJ, val_pull hJ, Category.assoc]

theorem isPullF_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Sp R)}
    {F : Type} [Field F] [Algebra (FractionRing R) F]
    {a : T'.left ⟶ T.left} {b : Sp F ⟶ T'.left} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPtF D F}
    (h : GtPt.IsPull a g g') (h' : GtPt.IsPullF F b g' g'') : GtPt.IsPullF F (b ≫ a) g g'' :=
  isPull_trans (T'' := TF (R := R) F) (g'' := ⟨g''.b, g''.s, g''.isGen, g''.s_zero, g''.mult⟩) h h'

theorem pair_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Sp R).Opens} {ψW : PsiOn D W} {k : ℕ}
    {T T' T'' : Over W.toScheme} {a : T' ⟶ T} {b : T'' ⟶ T'} {p : QkPtW D W ψW k T} {p' : QkPtW D W ψW k T'}
    {p'' : QkPtW D W ψW k T''} (h : QkPtW.IsPull a p p') (h' : QkPtW.IsPull b p' p'') :
    QkPtW.IsPull (b ≫ a) p p'' := by
  have h₁ : p''.y = p.y := Eq.trans h'.1 h.1
  have h₂ := isPull_trans (T := overW W T) (T' := overW W T') (T'' := overW W T'') (a := a.left) (b := b.left)
    (g := p.g) (g' := p'.g) (g'' := p''.g) h.2 h'.2
  exact ⟨h₁, h₂⟩

theorem pairF_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {W : (Sp R).Opens} {ψW : PsiOn D W} {k : ℕ}
    {F : Type} [Field F] [Algebra (FractionRing R) F]
    {T T' : Over W.toScheme} {a : T' ⟶ T} {x : Sp F ⟶ T'.left} {p : QkPtW D W ψW k T} {p' : QkPtW D W ψW k T'}
    {q : QkPt D F k} (h : QkPtW.IsPull a p p') (h' : QkPtW.IsPullF F x p' q) :
    QkPtW.IsPullF F (x ≫ a.left) p q := by
  have h₁ : q.y = p.y := Eq.trans h'.1 h.1
  have h₂ := isPullF_trans (T := overW W T) (T' := overW W T') (a := a.left) (b := x)
    (g := p.g) (g' := p'.g) (g'' := q.g) h.2 h'.2
  exact ⟨h₁, h₂⟩

theorem exists_isTorsMap :
    AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∃ f, IsTorsMap P ψW k f := by
  intro E _ _ _ H R _ _ _ _ hR t P W hW hp ψW k hk
  choose N p₀ hN using GlobalTheory.T.exists_torsion_pair_representative E H R hR t P W hW hp ψW k hk
  choose v hv hvF using fun y => GlobalTheory.T.exists_torsion_hom_image E H R hR t P W hW hp ψW k hk y (N y) (p₀ y) (hN y)
  choose c hc hu using fun y => (hN y).2.2.2
  have key : ∀ y T (p : QkPtW P.D.toPre W ψW k T) (hy : p.y = y),
      (Over.map W.ι).map (c p.y T p rfl) ≫ v p.y = (Over.map W.ι).map (c y T p hy) ≫ v y := by
    intro y T p hy
    subst hy
    rfl
  refine ⟨fun T p => (Over.map W.ι).map (c p.y T p rfl) ≫ v p.y, fun T p => ?_, fun T T' h p p' hh => ?_,
    fun F _ _ _ T x hx p q hq => ?_⟩
  · rw [← MonObj.comp_pow, hv, MonObj.comp_one]
  · have := hu p.y T' p' hh.1 (h ≫ c p.y T p rfl) (pair_trans (hc p.y T p rfl) hh)
    refine (key p.y T' p' hh.1).trans ?_
    rw [← this, Functor.map_comp, Category.assoc]
  · have e : (c p.y T p rfl).left ≫ (overW W (N p.y)).hom = (overW W T).hom :=
      Over.w ((Over.map W.ι).map (c p.y T p rfl))
    have hx' : OverGen F (overW W (N p.y)) (x ≫ (c p.y T p rfl).left) :=
      (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) e).trans hx)
    have := hvF p.y F (x ≫ (c p.y T p rfl).left) hx' q (pairF_trans (hc p.y T p rfl) hq)
    rw [Category.assoc] at this
    exact this

end GlobalTheory.FlatTors.TorsMapExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelTripleAmpleFramesComponent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory

theorem exists_zon_ampFrames_component :
    Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g n : ℕ), n.Prime → Odd n → ∃ k j₀ : ℕ, ∀ j ≥ j₀, ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (J : Type) (b : TBase o ((n ^ j) ^ 2)) (u : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap o R))) (t₀ : SAB H (Sp R)) (e : t₀.G ≅ u.A) (v : GlobalTheory.ZM.Ix g ((n ^ j) ^ 2) → R), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → IsMonHom e.hom → LBIso t₀.PP.L (u.L.pull e.hom.left) → u.HasTh (𝟙 _) v → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = (v i : Ω) / (v i' : Ω)})) Ω → ∃ C : ZOn (spMap (algebraMap o R)) t₀ (n ^ k), IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L ((n ^ k) ^ 2), A.r = r ∧ A.s = 1 := by
  intro h1 h2 hss hU hT hG E _ _ _ H g n hn ho
  obtain ⟨k, j₀, hk⟩ := GlobalTheory.exists_big_thetaSys_with_action h1 h2 E H g n hn ho
  refine ⟨k, j₀, ?_⟩
  intro j hj o Ω _ _ _ _ R J b u t₀ e v hR hfr he hL hth hfin
  obtain ⟨S, ρ, h, φ, act, hbig, hN, hfin', hcart, hLφ, hact, hadj, hprim⟩ :=
    hk j hj o Ω R J b u t₀ e v hR hfr he hL hth hfin
  have htests : S.HasTests := (GlobalTheory.T.thetaSystem_hasTests_of_real_point hss hU h1 h2 hT o Ω S ρ).1
  obtain ⟨m, a, GG, X, Z, U₀, EE, f, Xab, -, -, hNm, hO, hEE, -, -, -, hgen, hlast⟩ :=
    GlobalTheory.ZH.exists_minor_model o Ω S htests hfin'
  obtain ⟨Y⟩ := hG o Ω S ρ hbig Z U₀ EE hO hEE ⟨m, a, GG, hgen⟩
  have hopen : IsOpen (abLocus Y.G) := by
    rw [Y.ab]
    exact GlobalTheory.isOpen_setOf_TT_eq_bot o Ω S Z _ _ _ hO.div (fun z x₀ hx => (hlast z x₀ hx).2)
  obtain ⟨r₀, hr⟩ := GlobalTheory.exists_ampFrames_exponents h1 o Ω S ρ Z U₀ EE m a GG Y hNm hO hgen
  rw [hN] at hr
  exact GlobalTheory.T.exists_birationalModel_semiAbelian_ampleFrames h1 h2 E H o Ω R t₀ S ρ h φ act Z U₀ EE Y (n ^ k) r₀ hR hfr hO hopen hcart hLφ
    hact hadj hprim hr

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliPrimePowerFullLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_moduli_prime_power_fullLevel : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n : ℕ), 1 ≤ D.p + D.q → n.Prime → Odd n → ∃ j : ℕ, ∀ l : Level H, l.M = n → l.A = (n ^ j) ^ 2 → Nonempty (Moduli D l) := by
  first | exact @GlobalTheory.ZM.exists_moduli_prime_power_level | exact GlobalTheory.ZM.exists_moduli_prime_power_level | (intros; apply GlobalTheory.ZM.exists_moduli_prime_power_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelFamilyLocalisationPrimePowerLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegelFamily_localisation_prime_power_level : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → N0 := by
  first | exact @GlobalTheory.SiegelFromSharp.exists_siegelFamily | exact GlobalTheory.SiegelFromSharp.exists_siegelFamily | (intros; apply GlobalTheory.SiegelFromSharp.exists_siegelFamily <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientExistsListedKernelsSmoothBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkSplit

theorem exists_affine_isDomain {Z : Scheme.{0}} [IsLocallyNoetherian Z] (hZ : Geo.Tor.IsNormalScheme Z) (p : Z) :
    ∃ W : Z.Opens, IsAffineOpen W ∧ p ∈ W ∧ IsDomain Γ(Z, W) := by
  have := GlobalTheory.IsNormalScheme.of_pred hZ
  have hC := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents p)
  obtain ⟨W, hW, hpW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨_, hC⟩) (x := p) mem_irreducibleComponent
  exact ⟨W, hW, hpW, (GlobalTheory.IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible
    ⟨⟨p, hpW⟩, (isIrreducible_irreducibleComponent (x := p)).2.open_subset W.isOpen fun q hq => hle hq⟩).1⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_pull {S S' : Scheme.{0}} (s : S ⟶ Sp (KA l)) (f : S' ⟶ S) (o : Ob D l s) :
    ∃ o' : Ob D l (f ≫ s), Nonempty (ObjMap o' o f) :=
  GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S S' s (f ≫ s) f rfl rfl
    (by rw [show spMap (RingHom.id (KA l)) = 𝟙 _ from Spec.map_id _, Category.comp_id]) o

theorem hasQuot_image (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) {S S' : Scheme.{0}} [IsReduced S] [IsNoetherian S']
    (s : S ⟶ Sp (KA l)) (g : S' ⟶ S) [Etale g] (o : Ob D l s) (s' : S' ⟶ Sp (KA l)) (hs : s' = g ≫ s)
    (o' : Ob D l s') (m : ObjMap o' o g) (K : Set o.t.G.left) (hA : admitted l 𝔓 p) (hK : HeckeSet D o.t 𝔓 p i K)
    (hQ : HasQuot o' p (m.toSABMap.φ ⁻¹' K)) (q : S) (hq : q ∈ Set.range g) :
    ∃ (U : S.Opens) (o₁ : Ob D l (U.ι ≫ s)) (m₁ : ObjMap o₁ o U.ι), q ∈ U ∧ HasQuot o₁ p (m₁.toSABMap.φ ⁻¹' K) := by
  let U : S.Opens := ⟨Set.range g, g.isOpenMap.isOpen_range⟩
  obtain ⟨g', hg'⟩ : ∃ g' : S' ⟶ U.toScheme, g' ≫ U.ι = g :=
    ⟨IsOpenImmersion.lift U.ι g (by simp [U]), IsOpenImmersion.lift_fac _ _ _⟩
  have hU : ∀ x : S, x ∈ U → x ∈ Set.range g := fun _ h => h
  have hqU : q ∈ U := hq
  clear_value U
  subst hg'
  rw [Category.assoc] at hs
  subst hs
  obtain ⟨o₁, ⟨m₁⟩⟩ := exists_pull s U.ι o
  obtain ⟨m', hm'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o₁ o').2 U.ι g' m₁).2 m
  have he : Etale g' := Etale.of_comp g' U.ι
  have hsur : Surjective g' := ⟨fun y => by
    obtain ⟨x, hx⟩ := hU (U.ι y) y.2
    exact ⟨x, U.ι.isOpenEmbedding.injective (by simpa using hx)⟩⟩
  refine ⟨U, o₁, m₁, hqU, GlobalTheory.T.heckeQuotient_descends_etale_surjective_cover E H D l Xo 𝔓 p i _ _ _ g' o₁ o' m' _ hA
    (GlobalTheory.HkSetPull.heckeSet_pull D 𝔓 p i m₁.toSABMap K hK) he hsur inferInstance ?_⟩
  rw [hm', Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] at hQ
  exact hQ

end GlobalTheory.HkSplit

theorem GlobalTheory.hasQuot_of_lists_of_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s) (σ : Fin n → (𝟙_ (Over S) ⟶ o.t.G)) (K : Set o.t.G.left), 1 ≤ D.p + D.q → admitted l 𝔓 p → Smooth s → Lists (p ^ 2) σ K → HeckeSet D o.t 𝔓 p i K → HasQuot o p K := by
  intro E _ _ _ H D l Xo 𝔓 p i n S s o σ K hD hA hs hL hK
  obtain ⟨hr, hN, hn⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ S s hs
  refine GlobalTheory.T.heckeQuotient_of_open_cover_reduced_base E H D l Xo 𝔓 p i S s o K hA hK fun q => ?_
  obtain ⟨W, hW, hq, hd⟩ := GlobalTheory.HkSplit.exists_affine_isDomain hN q
  have hR : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  let j : Sp Γ(S, W) ⟶ S := hW.fromSpec
  have hj : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion hW.fromSpec)
  obtain ⟨x, hx⟩ : q ∈ Set.range j := by
    rw [show Set.range j = W from hW.range_fromSpec]; exact hq
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.HkSplit.exists_pull s j o
  obtain ⟨σ', -, hL'⟩ := GlobalTheory.HkSetPull.lists_pull m₁.toSABMap.cart K _ n σ hL
  obtain ⟨R', _, π, o', m, he, ⟨y, hy⟩, hQ⟩ := GlobalTheory.T.exists_etale_hasHeckeQuotient_noetherian_domain E H D l 𝔓 p i n Γ(S, W) (j ≫ s) o₁ σ' _ x hD hA hL'
    (GlobalTheory.HkSetPull.heckeSet_pull D 𝔓 p i m₁.toSABMap K hK)
  obtain ⟨m', hm'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o₁ o').2 j π m₁).1 m
  have : IsLocallyNoetherian (Sp R') := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsNoetherian (Sp R') := {}
  refine GlobalTheory.HkSplit.hasQuot_image Xo 𝔓 p i s (π ≫ j) o _ (Category.assoc _ _ _).symm o' m' K hA hK ?_ q
    ⟨y, by rw [Scheme.Hom.comp_apply, hy, hx]⟩
  rw [hm', Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  exact hQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptySiegelFamilyOverArithmeticBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_siegelFamily_over_arithmetic_base : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (h n : ℕ), 1 ≤ h → n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ), ArBase em → Nonempty (SFam h ((n ^ j) ^ 2) (b.ζ : o)) := by
  first | exact @GlobalTheory.ZM.SiegelArithFamily.nonempty_sFam | exact GlobalTheory.ZM.SiegelArithFamily.nonempty_sFam | (intros; apply GlobalTheory.ZM.SiegelArithFamily.nonempty_sFam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaObjectFamilyOpenClosureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_thetaObject_family_open_closure : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → Nonempty (ThetaFam n em C) := by
  first | exact @GlobalTheory.ZM.ThetaFamily.nonempty_thetaFam | exact GlobalTheory.ZM.ThetaFamily.nonempty_thetaFam | (intros; apply GlobalTheory.ZM.ThetaFamily.nonempty_thetaFam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationTriplesCompleteDVRTorsion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem LN.isAdmissible_of_complete_DVR_charZero (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (hV : LN.CDvr V) :
    LN.admitted V (IsLocalRing.maximalIdeal V) := by
  have := hV.1
  have := hV.2.1
  refine ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hV.2.1, hV.2.2, inferInstance, ?_⟩
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V)
  infer_instance

theorem LN.uDvrSt_holds : GlobalTheory.LN.UDvrSt := by
  obtain ⟨L, L2, L3, L4, L5, -⟩ := GlobalTheory.T.all_six_abelian_scheme_laws_hold
  intro E _ _ _ H V _ _ _ hV t hp hs
  have := hV.1
  exact GlobalTheory.T.exists_uniformisation_complete_local_normal_prime L L2 L3 L4 L5 LN.ega_holds GlobalTheory.T.uniformisation_completeDVR GlobalTheory.T.linearUniformisation_triples_torsion E H V _ (LN.isAdmissible_of_complete_DVR_charZero V hV)
    (by letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V); infer_instance) t hp hs
    (GlobalTheory.ThetaDvr.thetaNZ_of_polAt L L2 E H V t hp)

end GlobalTheory
end

