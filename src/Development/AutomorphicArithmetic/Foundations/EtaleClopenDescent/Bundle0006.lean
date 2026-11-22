import Mathlib
import Development.EtaleCohomology.EtaleSheaves.Bundle0077
import Development.EtaleCohomology.EtaleSheaves.LeafSHSysPf
import Development.EtaleCohomology.EtaleSheaves.Bundle0064
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0036
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0037

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.StrictlyHenselianLocalOfNegligibleDegree
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
open LateralTheory.E.E4 LateralTheory.E.StrictHenselianNeighbourhood

namespace UpperTheory.Cb

private theorem factor_later {B : Scheme.{0}} (U : B.Etale) (x : U.left) (Ω : Type) [Field Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ U.left) {J : Type} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (c : Cocone D) (V : J → B.Etale) (a : ∀ j, V j ⟶ U)
    (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j)) (e : ∀ j, Sp (D.obj j) ⟶ (V j).left)
    (t : Sp c.pt ⟶ U.left) (hP : IsPtNb U x Ω s D c V a l e t)
    (j : J) (E : Type) [CommRing E] [Algebra (D.obj j) E] [Algebra.Etale (D.obj j) E]
    (ψ : E →+* Ω)
    (hψ : Spec.map (CommRingCat.ofHom ψ) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (D.obj j) E)) = l j) :
    ∃ (k : J) (g : j ⟶ k) (φ : E →+* D.obj k), φ.comp (algebraMap (D.obj j) E) = (D.map g).hom ∧
      l k ≫ Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ) := by
  obtain ⟨-, he, hl, hcomp, -, hlc, hcof, heq⟩ := hP
  let π : Sp E ⟶ Sp (D.obj j) := Spec.map (CommRingCat.ofHom (algebraMap (D.obj j) E))
  haveI hπ : Etale π := HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr ‹_›)
  haveI : IsIso (e j) := he j
  let q : Sp E ⟶ (V j).left := π ≫ e j
  let W : B.Etale := Scheme.Etale.mk (q ≫ (V j).hom)
  let bj : W ⟶ V j := MorphismProperty.Over.homMk q rfl
  have hpt : Spec.map (CommRingCat.ofHom ψ) ≫ q = l j ≫ e j := by
    rw [← hψ]; simp [q, π]
  have hs : Spec.map (CommRingCat.ofHom ψ) ≫ q ≫ (a j).left = s := by
    rw [reassoc_of% hpt, hl]
  obtain ⟨k, g, hg, hgl⟩ := hcof W (bj ≫ a j) (Spec.map (CommRingCat.ofHom ψ)) hs
  obtain ⟨g', hg', hgl'⟩ : ∃ g' : (V k).left ⟶ Sp E, g' ≫ q ≫ (a j).left = (a k).left ∧
      l k ≫ e k ≫ g' = Spec.map (CommRingCat.ofHom ψ) := ⟨g, hg, hgl⟩
  clear hg hgl g hs
  let m := IsFiltered.max j k
  let u : j ⟶ m := IsFiltered.leftToMax j k
  let v : k ⟶ m := IsFiltered.rightToMax j k
  haveI : IsIso (e m) := he m
  let g1 : (V m).left ⟶ (V j).left :=
    inv (e m) ≫ Spec.map (CommRingCat.ofHom (D.map u).hom) ≫ e j
  let g2 : (V m).left ⟶ (V j).left :=
    inv (e m) ≫ Spec.map (CommRingCat.ofHom (D.map v).hom) ≫ e k ≫ g' ≫ q
  have h1 : g1 ≫ (a j).left = (a m).left := by
    simp only [g1, Category.assoc]; rw [hcomp j m u]; simp
  have h2 : g2 ≫ (a j).left = (a m).left := by
    simp only [g2, Category.assoc]; rw [hg', hcomp k m v]; simp
  have h3 : l m ≫ e m ≫ g1 = l m ≫ e m ≫ g2 := by
    simp only [g1, g2, IsIso.hom_inv_id_assoc]
    rw [reassoc_of% (hlc j m u), reassoc_of% (hlc k m v), reassoc_of% hgl', hpt]
  obtain ⟨n, w, hw⟩ := heq (V j) (a j) m g1 g2 h1 h2 h3
  simp only [g1, g2, IsIso.hom_inv_id_assoc] at hw
  let h : Sp (D.obj n) ⟶ Sp E :=
    Spec.map (CommRingCat.ofHom (D.map w).hom) ≫ Spec.map (CommRingCat.ofHom (D.map v).hom) ≫
      e k ≫ g'
  have hh : h ≫ π = Spec.map (CommRingCat.ofHom (D.map (u ≫ w)).hom) := by
    rw [← cancel_mono (e j)]
    have : Spec.map (CommRingCat.ofHom (D.map (u ≫ w)).hom) =
        Spec.map (CommRingCat.ofHom (D.map w).hom) ≫ Spec.map (CommRingCat.ofHom (D.map u).hom) := by
      rw [← Spec.map_comp]; simp
    rw [this]
    simp only [Category.assoc]
    rw [hw]
    simp [h, q]
  refine ⟨n, u ≫ w, (Spec.preimage h).hom, ?_, ?_⟩
  · have h4 : Spec.map (CommRingCat.ofHom (algebraMap (D.obj j) E) ≫ Spec.preimage h) =
        Spec.map (CommRingCat.ofHom (D.map (u ≫ w)).hom) := by
      rw [Spec.map_comp, Spec.map_preimage]; exact hh
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h4)
  · rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    simp only [h]
    rw [reassoc_of% (hlc m n w), reassoc_of% (hlc k m v), hgl']

end UpperTheory.Cb

theorem UpperTheory.Cb.strictlyHenselianLocal_of_negligibleDegree :
    LateralTheory.E.LeafDegCut.LeafNeg → LateralTheory.E.StrictHenselianNeighbourhood.LeafSHHens := by
  intro _ B U x Ω _ _ s J _ _ D c hc V a l e t hP _
  let ρ : ∀ j, D.obj j ⟶ CommRingCat.of Ω := fun j => Spec.preimage (l j)
  have hρ : ∀ j, Spec.map (ρ j) = l j := fun j => Spec.map_preimage _
  have hlc := hP.2.2.2.2.2.1
  have hw : ∀ (j k : J) (f : j ⟶ k), D.map f ≫ ρ k = ρ j := by
    intro j k f
    apply Spec.map_injective
    rw [Spec.map_comp, hρ, hρ, ← hlc j k f]
    rfl
  let cc : Cocone D :=
    { pt := CommRingCat.of Ω
      ι := { app := ρ, naturality := fun j k f => by simpa using hw j k f } }
  let ω : c.pt →+* Ω := (hc.desc cc).hom
  have hω : ∀ j, ω.comp (c.ι.app j).hom = (ρ j).hom := fun j =>
    congrArg CommRingCat.Hom.hom (hc.fac cc j)
  refine LateralTheory.E.LeafSHSysPf.SHofCof D c hc ⟨Ω, inferInstance, inferInstance, ω, ?_⟩
  intro j E _ _ _ ψ hψ
  obtain ⟨k, g, φ, h1, h2⟩ := factor_later U x Ω s D c V a l e t hP j E ψ (by
    rw [← Spec.map_comp, ← hρ j]
    congr 1
    apply CommRingCat.hom_ext
    rw [hω j] at hψ
    exact hψ)
  refine ⟨k, g, φ, h1, ?_⟩
  rw [← RingHom.comp_assoc, hω k]
  have h3 : CommRingCat.ofHom φ ≫ ρ k = CommRingCat.ofHom ψ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ]
    exact h2
  exact congrArg CommRingCat.Hom.hom h3
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TwistedSectionsOfNegativeDegreeVanishing
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Cb.LocalTwistForms

set_option backward.isDefEq.respectTransparency false in
private theorem covPt {X : Scheme.{0}} (S : Sieve X) (hS : S ∈ Scheme.etaleTopology X) (x : X) :
    ∃ (V : Scheme.{0}) (f : V ⟶ X) (_ : Etale f) (y : V), S f ∧ f y = x := by
  obtain ⟨𝒰, hle⟩ := Scheme.mem_grothendieckTopology_iff.1 hS
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  exact ⟨𝒰.X i, 𝒰.f i, inferInstance, y, hle _ _ ⟨i⟩, rfl⟩

private theorem res_res {R : Type} [CommRing R] {F : Shv R} {V' V U : Scheme.{0}} (g : V' ⟶ V) (h : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.res h x) = Sec.res (g ≫ h) x := by
  simp [Sec.res, op_comp, Functor.map_comp]

private theorem res_smul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (c : ULift.{1} R) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x := map_smul _ _ _

private theorem sec_res (q : ℕ) (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (x : (twF q i).obj Γ(U, ⊤)) :
    (Sec.res g (ofRings.sec (twF q i) U x) : Sec (tw q i) V) = ofRings.sec (twF q i) V ((twF q i).map g.appTop x) :=
  (NatTrans.naturality_apply (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) g.op x).symm

private theorem map_single (q : ℕ) (i : ℤ) {A B : CommRingCat.{0}} (φ : A ⟶ B) (ζ : Prim q A) (b : ULift.{1} (ZMod q)) :
    (twF q i).map φ (Submodule.Quotient.mk (Finsupp.single ζ b) : (twF q i).obj A) =
      (Submodule.Quotient.mk (Finsupp.single (Prim.map φ.hom ζ) b) : (twF q i).obj B) := by
  change Submodule.Quotient.mk (Finsupp.mapDomain _ _) = _
  rw [Finsupp.mapDomain_single]

private theorem twGen_res (q : ℕ) (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (Prim.map g.appTop.hom ζ) := by
  exact (sec_res q i g _).trans (congrArg _ (map_single q i g.appTop ζ 1))

private theorem unit_res {X : Scheme.{0}} {A B C : X.Opens} (h₁ : B ≤ A) (h₂ : C ≤ A) (h₃ : C ≤ B) (f : Γ(X, A))
    (hu : IsUnit (X.presheaf.map (homOfLE h₁).op f)) : IsUnit (X.presheaf.map (homOfLE h₂).op f) := by
  have e : X.presheaf.map (homOfLE h₂).op = X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₃).op := by
    rw [← Functor.map_comp]; rfl
  rw [e, CommRingCat.comp_apply]
  exact hu.map _

private theorem sheafDetect (q : ℕ) [NeZero q] (i : ℤ) (X : Scheme.{0}) [Nonempty X] (ζ : Prim q Γ(X, ⊤))
    (c : ULift.{1} (ZMod q)) (h : c • twGen i ζ = 0) : c = 0 := by
  let e : (twF q i).obj Γ(X, ⊤) := c • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(X, ⊤))
  have h0 : ofRings.sec (twF q i) X e = ofRings.sec (twF q i) X 0 := by
    refine Eq.trans ?_ (h.trans (map_zero _).symm)
    exact map_smul _ _ _
  have hmem := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) (X := op X) e 0 h0
  obtain ⟨V, f, -, y, hf, -⟩ := covPt _ hmem (Classical.arbitrary X)
  have hf' : (twF q i).map f.appTop e = 0 := Eq.trans hf (map_zero ((twF q i).map f.appTop).hom)
  have e1 : (twF q i).map f.appTop e =
      c • (twF q i).map f.appTop (Submodule.Quotient.mk (Finsupp.single ζ 1) : (twF q i).obj Γ(X, ⊤)) :=
    map_smul ((twF q i).map f.appTop).hom c _
  have : Nontrivial Γ(V, ⊤) := (V.presheaf.germ ⊤ y trivial).hom.domain_nontrivial
  rw [e1, map_single] at hf'
  exact UpperTheory.twist_generator_smul_eq_zero_imp q i Γ(V, ⊤) _ c hf'

private theorem twLocal (q : ℕ) [NeZero q] (i : ℤ) (A : CommRingCat.{0}) (ζ : Prim q A) (t : (twF q i).obj A)
    (p : Ideal A) [p.IsPrime] :
    ∃ f : A, f ∉ p ∧ ∀ (B : CommRingCat.{0}) (φ : A ⟶ B), IsUnit (φ f) → ∃ c : ULift.{1} (ZMod q),
      (twF q i).map φ t = c • (Submodule.Quotient.mk (Finsupp.single (Prim.map φ.hom ζ) 1) : (twF q i).obj B) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  induction x using Finsupp.induction_linear with
  | zero =>
    refine ⟨1, fun h => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h), fun B φ _ => ⟨0, ?_⟩⟩
    rw [zero_smul]
    exact map_zero ((twF q i).map φ).hom
  | add x y hx hy =>
    obtain ⟨f, hf, H⟩ := hx
    obtain ⟨g, hg, H'⟩ := hy
    refine ⟨f * g, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hf hg, fun B φ hu => ?_⟩
    rw [map_mul] at hu
    obtain ⟨c, hc⟩ := H B φ (isUnit_of_mul_isUnit_left hu)
    obtain ⟨d, hd⟩ := H' B φ (isUnit_of_mul_isUnit_right hu)
    refine ⟨c + d, ?_⟩
    rw [add_smul, ← hc, ← hd]
    exact map_add ((twF q i).map φ).hom (Submodule.Quotient.mk x : (twF q i).obj A) (Submodule.Quotient.mk y : (twF q i).obj A)
  | single ξ b =>
    obtain ⟨f, a, hf, H⟩ := UpperTheory.primitive_root_eq_pow_locally q A ξ ζ p
    refine ⟨f, hf, fun B φ hu => ⟨b * ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q), ?_⟩⟩
    rw [map_single]
    have hmem : Finsupp.single (Prim.map φ.hom ξ) 1 - Finsupp.single (Prim.map φ.hom ζ) (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q))
        ∈ twRel q i B :=
      Submodule.subset_span ⟨Prim.map φ.hom ζ, Prim.map φ.hom ξ, a, H B φ.hom hu, rfl⟩
    have e1 : (Submodule.Quotient.mk (Finsupp.single (Prim.map φ.hom ξ) 1) : (twF q i).obj B) =
        Submodule.Quotient.mk (Finsupp.single (Prim.map φ.hom ζ) (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q))) :=
      (Submodule.Quotient.eq _).2 hmem
    have e2 : ∀ (η : Prim q B) (r : ULift.{1} (ZMod q)), (Submodule.Quotient.mk (Finsupp.single η r) : (twF q i).obj B) =
        r • (Submodule.Quotient.mk (Finsupp.single η 1) : (twF q i).obj B) := by
      intro η r
      refine Eq.trans ?_ (Submodule.Quotient.mk_smul _ _ _)
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [e2 _ b, e1, e2 _ (ULift.up _), smul_smul]

private theorem formP (q : ℕ) [NeZero q] (i : ℤ) (X : Scheme.{0}) (hX : IsUnit ((q : ℕ) : Γ(X, ⊤)))
    (s : Sec (tw q i) X) (x : X) :
    ∃ (V : Scheme.{0}) (f : V ⟶ X) (_ : Etale f) (y : V) (ζ : Prim q Γ(V, ⊤)) (c : ULift.{1} (ZMod q)),
      f y = x ∧ Sec.res f s = c • twGen i ζ := by
  obtain ⟨V₁, f₁, h₁, y₁, ζ₁, rfl⟩ := UpperTheory.exists_etale_nbhd_primitiveRoot_of_isUnit_natCast q X hX x
  have hmem := Presheaf.imageSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) (U := op V₁) (Sec.res f₁ s)
  obtain ⟨V₂, f₂, h₂, y₂, ⟨t, ht⟩, rfl⟩ := covPt _ hmem y₁
  let ρ : Γ(V₂, ⊤) ⟶ V₂.residueField y₂ := V₂.presheaf.germ ⊤ y₂ trivial ≫ V₂.residue y₂
  have hp : (RingHom.ker ρ.hom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨f, hfp, H⟩ := twLocal q i Γ(V₂, ⊤) (Prim.map f₂.appTop.hom ζ₁) t (RingHom.ker ρ.hom)
  have hy : y₂ ∈ V₂.basicOpen f := by
    rw [Scheme.mem_basicOpen_top]
    have h1 : (V₂.residue y₂).hom ((V₂.presheaf.germ ⊤ y₂ trivial).hom f) ≠ 0 := fun h => hfp (RingHom.mem_ker.2 h)
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).1 h1
  have hu : IsUnit ((V₂.basicOpen f).ι.appTop f) := by
    have h0 := V₂.toRingedSpace.isUnit_res_basicOpen f
    rw [Scheme.Opens.ι_appTop]
    exact unit_res _ _ (le_of_eq (by simp; rfl)) f h0
  obtain ⟨c, hc⟩ := H _ (V₂.basicOpen f).ι.appTop hu
  refine ⟨V₂.basicOpen f, (V₂.basicOpen f).ι ≫ f₂ ≫ f₁, inferInstance, ⟨y₂, hy⟩,
    Prim.map (V₂.basicOpen f).ι.appTop.hom (Prim.map f₂.appTop.hom ζ₁), c, by simp; rfl, ?_⟩
  rw [← res_res, ← res_res]
  have ht' : Sec.res f₂ (Sec.res f₁ s) = ofRings.sec (twF q i) V₂ t := ht.symm
  refine (congrArg (Sec.res (V₂.basicOpen f).ι) ht').trans ((sec_res q i _ t).trans
    ((congrArg (ofRings.sec (twF q i) _) hc).trans ?_))
  exact map_smul _ _ _

end UpperTheory.Cb.LocalTwistForms

open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafInj0WPf LateralTheory.E.LeafDegCut UpperTheory.Cb.LocalTwistForms in
theorem UpperTheory.Cb.twistedSections_of_negativeDegreeVanishing :
    LateralTheory.E.LeafDegCut.LeafNeg → LateralTheory.E.LeafInj0WPf.LeafSecTw := by
  intro _ q _ k _ hq i B W s₀ ι _ U s hs x hx
  have hX : IsUnit ((q : ℕ) : Γ(U.left, ⊤)) := by
    have h := hq.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (U.hom ≫ s₀).appTop).hom
    simpa using h
  obtain ⟨V, f, hf, y, ζ, c, hy, hsV⟩ := formP q i U.left hX s x
  let U' : B.Etale := MorphismProperty.Over.mk ⊤ (f ≫ U.hom) (inferInstanceAs (Etale (f ≫ U.hom)))
  let a : U' ⟶ U := MorphismProperty.Over.homMk f rfl
  refine ⟨U', a, y, hy, ?_⟩
  obtain ⟨w, hw⟩ := hx
  have hne : Nonempty ↥(pullback U'.hom ι) := by
    have e : U'.hom y = ι w := by
      rw [hw, ← hy]
      rfl
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback y w e
    exact ⟨z⟩
  have hc : c = 0 := by
    have e : prB ι U' ≫ f = resBW ι a ≫ prB ι U := (pullback.lift_fst _ _ _).symm
    have h1 : Sec.res (prB ι U') (Sec.res f s) = 0 := by
      have h0 := congrArg (Sec.res (resBW ι a)) hs
      rw [res_res, ← e] at h0
      exact (res_res _ _ _).trans (h0.trans (map_zero _))
    have key : ∀ pr : pullback U'.hom ι ⟶ V, Sec.res pr (Sec.res f s) = 0 → c = 0 := fun pr h => by
      rw [hsV, res_smul, twGen_res] at h
      exact sheafDetect q i _ _ c h
    exact key (prB ι U') h1
  change Sec.res f s = 0
  rw [hsV, hc, zero_smul]
end
end

