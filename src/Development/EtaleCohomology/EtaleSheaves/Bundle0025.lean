import Development.EtaleCohomology.EtaleSheaves.Bundle0007
import Development.EtaleCohomology.TateTwists.Bundle0007
import Development.EtaleCohomology.EtaleSheaves.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.EtaleCohomology.EtaleSheaves.Bundle0012
import Development.EtaleCohomology.EtaleSheaves.Bundle0006
import Development.EtaleCohomology.EtaleSheaves.LeafSSCut

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafOneSpecPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafOneSpecPf

open LateralTheory.E.CupProductRingLaws

theorem res_neg_zero (R : Type) [CommRing R] (F : Shv R) (n : ℤ) (hn : n < 0) : IsZero ((res R F).X n) := by
  unfold res
  unfold InjectiveResolution.cochainComplex
  apply HomologicalComplex.isZero_extend_X
  rintro i rfl
  change ((i : ℤ)) < 0 at hn
  omega
theorem chains_pos_zero (R : Type) [CommRing R] (E : Spc) (n : ℤ) (hn : 0 < n) : IsZero (((chains R).obj E).X n) := by
  unfold chains
  simp only [Functor.comp_obj, ComplexShape.Embedding.extendFunctor_obj]
  apply HomologicalComplex.isZero_extend_X
  rintro i rfl
  change 0 < -((i : ℤ)) at hn
  omega
theorem free_hom_ext (R : Type) [CommRing R] (P : PSh) (G : Shv R) (f g : (free R).obj P ⟶ G)
    (h : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (f.hom.app (op U)).hom (freeGen R P U x) = (g.hom.app (op U)).hom (freeGen R P U x)) :
    f = g := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ G.property
  ext U : 2
  apply ModuleCat.free_hom_ext
  intro x
  exact h U.unop x.down
theorem cochain0_ext (R : Type) [CommRing R] (F : Shv R) (E : Spc)
    (α β : Cochain ((chains R).obj E) (res R F) 0)
    (h : ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev α 0 0 (by simp) U x = ev β 0 0 (by simp) U x) : α = β := by
  apply Cochain.ext
  intro p q hpq
  rcases lt_trichotomy p 0 with hp | rfl | hp
  · exact (res_neg_zero R F q (by omega)).eq_of_tgt _ _
  · have key : (chainsXIso R E 0).inv ≫ α.v (-((0 : ℕ) : ℤ)) 0 (by simp) =
        (chainsXIso R E 0).inv ≫ β.v (-((0 : ℕ) : ℤ)) 0 (by simp) :=
      free_hom_ext R _ _ _ _ (fun U x => h U x)
    obtain rfl : q = 0 := by omega
    simpa using key
  · exact (chains_pos_zero R E p hp).eq_of_src _ _

def LeafCochain0Ext : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc)
  (α β : Cochain ((chains R).obj E) (res R F) 0),
  (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev α 0 0 (by simp) U x = ev β 0 0 (by simp) U x) → α = β

theorem leafCochain0Ext_pf : LeafCochain0Ext := fun R _ F E α β h => cochain0_ext R F E α β h

def LeafOneExists : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → ∃ α, IsOneCocycle q E α

def LeafPrimCover : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
  ∃ S : Sieve U, S ∈ Scheme.etaleTopology U ∧ ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Nonempty (Prim q Γ(V, ⊤))

def LeafSecPrimLocal : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (q : ℕ) [NeZero q] (U : Scheme.{0}) (a b : Sec F U),
  IsUnit (q : Γ(U, ⊤)) → (∀ (V : Scheme.{0}) (g : V ⟶ U), Nonempty (Prim q Γ(V, ⊤)) → Sec.res g a = Sec.res g b) → a = b

theorem sec_sep (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U)
    (a b : Sec F U) (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec.res g a = Sec.res g b) : a = b := by
  have hF := (Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.property
  rw [isSheaf_iff_isSheaf_of_type] at hF
  exact (hF S hS).isSeparatedFor.ext (fun V g hg => h V g hg)

theorem leafSecPrimLocal_of (hP : LeafPrimCover) : LeafSecPrimLocal := by
  intro R _ F q _ U a b hq h
  obtain ⟨S, hS, hSP⟩ := hP q U hq
  exact sec_sep R F U S hS a b fun V g hg => h V g (hSP V g hg)

theorem one_cocycle_eq (hB : LeafCochain0Ext) (hC : LeafSecPrimLocal) (q : ℕ) [NeZero q] (E : Spc) (hE : Inv q E)
    (α β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) (hα : IsOneCocycle q E α) (hβ : IsOneCocycle q E β) :
    α = β := by
  apply Subtype.ext
  apply hB (ZMod q) (tw q 0) E α.1 β.1
  intro U x
  refine hC (ZMod q) _ q U _ _ (hE U ⟨x⟩) ?_
  rintro V g ⟨ζ⟩
  rw [← LateralTheory.EtaleFoundations.ev_nat_pf α.1 0 0 (by simp) g x, ← LateralTheory.EtaleFoundations.ev_nat_pf β.1 0 0 (by simp) g x]
  exact (hα V _ ζ).trans (hβ V _ ζ).symm

theorem LeafOneSpec_of (hA : LeafOneExists) (hP : LeafPrimCover) : LeafOneSpec := by
  have hB := leafCochain0Ext_pf
  have hC := leafSecPrimLocal_of hP
  intro q _ E hE
  refine ⟨hA q E hE, fun α hα => ?_⟩
  obtain ⟨α₀, h₀⟩ := hA q E hE
  obtain ⟨α₁, h₁, hα₁⟩ := pick_spec (P := fun c : Ht q E 0 0 => ∃ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0,
    CohomologyClass.mk α = c ∧ ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)),
      ev α.1 0 0 (by simp) U x = resGen 0 ζ) ⟨CohomologyClass.mk α₀, α₀, rfl, h₀⟩
  change pick _ = _
  rw [← h₁, one_cocycle_eq hB hC q E hE α₁ α hα₁ hα]

end LateralTheory.E.LeafOneSpecPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafRepVanishPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafRepVanishPf

variable (R : Type) [CommRing R]

theorem free_mono {P Q : PSh} (φ : P ⟶ Q) [Mono φ] : Mono ((free R).map φ) := by
  have : Mono ((freeP R).map φ) := by
    rw [NatTrans.mono_iff_mono_app]
    intro Y
    rw [ModuleCat.mono_iff_injective]
    have hi : Function.Injective (φ.app Y) := (mono_iff_injective _).1 inferInstance
    have hu : Function.Injective (uliftFunctor.{1}.map (φ.app Y)) := by
      intro a b h; exact ULift.ext _ _ (hi (congrArg ULift.down h))
    exact Finsupp.mapDomain_injective hu
  unfold free
  simp only [Functor.comp_map]
  infer_instance

theorem chains_f (E E' : Spc) (f : E ⟶ E') (N : ℕ) :
    ((chains R).map f).f (-(N : ℤ)) = (chainsXIso R E N).hom ≫ (free R).map (f.app (op (SimplexCategory.mk N))) ≫ (chainsXIso R E' N).inv := by
  exact (HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := N) rfl).trans rfl

theorem freeGen_nat {P Q : PSh} (φ : P ⟶ Q) (Y : Scheme.{0}) (x : P.obj (op Y)) :
    (((free R).map φ).hom.app (op Y)).hom (freeGen R P Y x) = freeGen R Q Y (φ.app _ x) := by
  have e := congrArg (fun t => (t.app (op Y)).hom (ModuleCat.freeMk (ULift.up.{1} x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map φ))
  have e2 : (((freeP R).map φ).app (op Y)).hom (ModuleCat.freeMk (ULift.up.{1} x)) =
      ModuleCat.freeMk (ULift.up.{1} (φ.app _ x)) := ModuleCat.free_map_apply _ _
  simp only [NatTrans.comp_app, ModuleCat.hom_comp] at e
  refine e.symm.trans ?_
  exact congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op Y))) e2

theorem ev_pull {U E : Spc} (f : U ⟶ E) {K : Cx R} {n : ℤ} (γ : Cochain ((chains R).obj E) K n) (N : ℕ) (w : ℤ)
    (h : -(N : ℤ) + n = w) (Y : Scheme.{0}) (y : Sx U N Y) :
    ev ((Cochain.ofHom ((chains R).map f)).comp γ (zero_add n)) N w h Y y = ev γ N w h Y ((f.app _).app _ y) := by
  unfold ev
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, chains_f]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← freeGen_nat]
  rfl

theorem chains_mono {U E : Spc} (f : U ⟶ E) [Mono f] (p : ℤ) : Mono (((chains R).map f).f p) := by
  by_cases hp : p ≤ 0
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨p.natAbs, by omega⟩
    rw [chains_f]
    have := free_mono R (f.app (op (SimplexCategory.mk N)))
    infer_instance
  · have hz : IsZero (((chains R).obj U).X p) :=
      HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
        change -(i : ℤ) = p at hi; omega)
    exact ⟨fun a b _ => hz.eq_of_tgt a b⟩

theorem LeafRepVanish_of : LateralTheory.E.LeafA6suppPf.LeafRepVanish := by
  intro R _ U E f hf F n a ha
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective a
  have hg := chains_mono R f
  have hinj : ∀ q, Injective ((res R F).X q) := fun q =>
    (inferInstance : Injective ((injectiveResolution F).cochainComplex.X q))
  have h1 : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) α (zero_add n)) = 0 := ha
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at h1
  obtain ⟨β', hβ'⟩ := h1
  let β : Cochain ((chains R).obj E) (res R F) (n - 1) :=
    Cochain.mk fun p q hpq => Injective.factorThru (β'.v p q hpq) (((chains R).map f).f p)
  have hβ : (Cochain.ofHom ((chains R).map f)).comp β (zero_add _) = β' := by
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
    simp only [β, Cochain.mk_v]
    exact Injective.comp_factorThru _ _
  let b : Cocycle ((chains R).obj E) (res R F) n := Cocycle.mk (δ (n - 1) n β) (n + 1) rfl (δ_δ _ _ _ _)
  refine ⟨α - b, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, (CohomologyClass.mk_eq_zero_iff b).2
      ((mem_coboundaries_iff b (n - 1) (by omega)).2 ⟨β, rfl⟩), sub_zero]
  · intro N w h Y y
    rw [← ev_pull]
    have e : (Cochain.ofHom ((chains R).map f)).comp (α - b).1 (zero_add n) = 0 := by
      rw [Cocycle.coe_sub, Cochain.comp_sub]
      have : (Cochain.ofHom ((chains R).map f)).comp (b : Cochain _ _ n) (zero_add n) = δ (n - 1) n β' := by
        rw [← hβ]; simp [b]
      rw [this, hβ']
      simp [zcomp]
    rw [e]
    simp [ev]

end LateralTheory.E.LeafRepVanishPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafRingUnitPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafRingUnitPf
open LateralTheory.E.CupProductRingLaws

def UnitProp {q : ℕ} {i : ℤ} (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q (0 + i)))) : Prop :=
  ∀ (U : Scheme.{0}) (t w : ℤ) (h : 0 + t = w) (a : Sec ((res _ (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
    Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g a = resGen 0 ζ) → HEq (μ.mul U 0 t w h a b) b

def LeafUnitPair : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ),
  ∃ μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q (0 + i))), IsTwPair μ ∧ UnitProp μ

def OneLoc {q : ℕ} {E : Spc} (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) : Prop :=
  ∀ (U : Scheme.{0}) (x : Sx E 0 U), Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g (ev α.1 0 0 (by simp) U x) = resGen 0 ζ)

def LeafOneLoc : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E →
  ∀ α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, IsOneCocycle q E α → OneLoc α

def LeafUnitAW : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc) (i : ℤ)
  (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q (0 + i)))), UnitProp μ →
  ∀ (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0), OneLoc α →
  ∀ (n : ℤ) (β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q i)) n),
    ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q (0 + i))) (0 + n), μ.IsAW rfl α.1 β.1 γ.1 ∧
      CohomologyClass.mk γ = Ht.cast (by ring) (by ring) (CohomologyClass.mk β : Ht q E n i)

theorem LeafRingUnit_of (hcup : LeafCupSpec) (hex : LeafTwPairExists) (hun : LeafTwPairUnique) (hone : LeafOneSpec)
    (h1 : LeafUnitPair) (h2a : LeafOneLoc) (h2 : LeafUnitAW) : LeafRingUnit := by
  intro q _ E hE n i a
  obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨μ, hμ, hU⟩ := h1 q i
  obtain ⟨⟨α, hα⟩, hαone⟩ := hone q E hE
  obtain ⟨γ, hγ, hγc⟩ := h2 q E i μ hU α (h2a q E hE α hα) n β
  have htw : IsTwPair (twPair q 0 i) := pick_spec (hex q 0 i)
  have hc : cup q (one q E) (CohomologyClass.mk β) = (twPair q 0 i).cup E rfl (one q E) (CohomologyClass.mk β) := rfl
  rw [hc, hun q 0 i _ μ htw hμ E rfl, hαone α hα, (hcup (ZMod q) μ E rfl).2 α β γ hγ, hγc]

end LateralTheory.E.LeafRingUnitPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSelPicPf
section
noncomputable section
open nonZeroDivisors IsDedekindDomain

namespace LateralTheory.E.LeafSelPicPf
open LateralTheory.E.LeafPicCut

lemma units_torsionFree {B : Type} [CommRing B] [IsDedekindDomain B] {q : ℕ} (hq : q ≠ 0)
    (x : (FractionalIdeal B⁰ (FractionRing B))ˣ) (h : x ^ q = 1) : x = 1 := by
  have hx0 : (x : FractionalIdeal B⁰ (FractionRing B)) ≠ 0 := x.ne_zero
  have hc : ∀ v : HeightOneSpectrum B,
      FractionalIdeal.count (FractionRing B) v (x : FractionalIdeal B⁰ (FractionRing B)) = 0 := by
    intro v
    have h1 := FractionalIdeal.count_pow (FractionRing B) v q (x : FractionalIdeal B⁰ (FractionRing B))
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one, FractionalIdeal.count_one] at h1
    have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq
    exact (mul_eq_zero.mp h1.symm).resolve_left hq'
  ext1
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' (FractionRing B) hx0]
  simp [hc]

lemma exists_rep {B : Type} [CommRing B] [IsDedekindDomain B] (q : ℕ) (c : ClassGroup B) (hc : c ^ q = 1) :
    ∃ (I : (FractionalIdeal B⁰ (FractionRing B))ˣ) (f : (FractionRing B)ˣ),
      ClassGroup.mk (FractionRing B) I = c ∧ toPrincipalIdeal B (FractionRing B) f = I ^ q := by
  revert hc
  refine ClassGroup.induction (R := B) (FractionRing B) (fun I hc => ?_) c
  · refine ⟨I, ?_⟩
    have h1 : ClassGroup.mk (FractionRing B) (I ^ q) = ClassGroup.mk (FractionRing B) 1 := by
      rw [map_pow, hc, map_one]
    obtain ⟨x, hx⟩ := ClassGroup.mk_eq_mk.mp h1
    refine ⟨x⁻¹, rfl, ?_⟩
    rw [map_inv, inv_eq_iff_mul_eq_one, mul_comm, hx]

theorem LeafSelPic_of : LeafSelPic := by
  intro B _ _ q _ hfin
  classical
  have hex := fun c : {c : ClassGroup B // c ^ q = 1} => exists_rep q c.1 c.2
  choose I f hI hf using hex
  have hsel : ∀ c, f c ∈ sel B q := fun c => by
    simp only [sel, Subgroup.mem_comap, MonoidHom.mem_range]
    exact ⟨I c, by rw [hf c]; rfl⟩
  let φ : {c : ClassGroup B // c ^ q = 1} → selQ B q := fun c => QuotientGroup.mk ⟨f c, hsel c⟩
  refine Finite.of_injective φ ?_
  intro c d hcd
  have h1 := QuotientGroup.eq.mp hcd
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range] at h1
  obtain ⟨u, hu⟩ := h1
  simp only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hu
  have hx : ((I c)⁻¹ * I d * (toPrincipalIdeal B (FractionRing B) u)⁻¹) ^ q = 1 := by
    rw [mul_pow, mul_pow, inv_pow, inv_pow, ← map_pow, hu, ← hf c, ← hf d, map_mul, map_inv]
    group
  have h2 := units_torsionFree (NeZero.ne q) _ hx
  apply Subtype.ext
  rw [← hI c, ← hI d]
  refine ClassGroup.mk_eq_mk.mpr ⟨u, ?_⟩
  rw [mul_inv_eq_one, inv_mul_eq_iff_eq_mul] at h2
  exact h2.symm

end LateralTheory.E.LeafSelPicPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafSqPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC LateralTheory.E.t_E6Cut LateralTheory.E.LeafExcPf

namespace LateralTheory.E.LeafSqPf

def LeafSqFree : Prop := ∀ (R : Type) [CommRing R] {P U E' E : PSh} (fst : P ⟶ U) (snd : P ⟶ E') (f : U ⟶ E) [Mono f]
  (g : E' ⟶ E), IsPullback fst snd f g →
  (∀ (T : Scheme.{0}) (y : E.obj (op T)), EtLoc T fun V k =>
    (∃ u : U.obj (op V), f.app (op V) u = E.map k.op y) ∨ ∃ a : E'.obj (op V), g.app (op V) a = E.map k.op y) →
  (∀ (T : Scheme.{0}) (a b : E'.obj (op T)), g.app (op T) a = g.app (op T) b → EtLoc T fun V k =>
    E'.map k.op a = E'.map k.op b ∨ ∃ u : U.obj (op V), f.app (op V) u = E.map k.op (g.app (op T) a)) →
  IsPushout ((free R).map snd) ((free R).map fst) ((free R).map g) ((free R).map f)

theorem sq_comm (R : Type) [CommRing R] {U E' E : Spc} (f : U ⟶ E) (g : E' ⟶ E) (n : ℤ) :
    ((chains R).map (pullback.snd f g)).f n ≫ ((chains R).map g).f n =
      ((chains R).map (pullback.fst f g)).f n ≫ ((chains R).map f).f n := by
  rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, ← Functor.map_comp, ← Functor.map_comp,
    pullback.condition]

theorem LeafSq_of (hFree : LeafSqFree) : LeafSq := by
  intro R _ U E' E f _ g h1 h2 n
  by_cases h : ∃ p : ℕ, ComplexShape.embeddingDownNat.f p = n
  · obtain ⟨p, hp⟩ := h
    have hpb : IsPullback ((pullback.fst f g).app (op (SimplexCategory.mk p)))
        ((pullback.snd f g).app (op (SimplexCategory.mk p)))
        (f.app (op (SimplexCategory.mk p))) (g.app (op (SimplexCategory.mk p))) :=
      (IsPullback.of_hasPullback f g).map ((evaluation _ _).obj (op (SimplexCategory.mk p)))
    have : Mono (f.app (op (SimplexCategory.mk p))) := (NatTrans.mono_iff_mono_app f).1 ‹_› _
    have key := hFree R _ _ _ _ hpb (fun T y => h1 p T y) (fun T a b hab => h2 p T a b hab)
    show IsPushout (HomologicalComplex.extendMap ((chainsN R).map (pullback.snd f g)) ComplexShape.embeddingDownNat |>.f n)
      (HomologicalComplex.extendMap ((chainsN R).map (pullback.fst f g)) ComplexShape.embeddingDownNat |>.f n)
      (HomologicalComplex.extendMap ((chainsN R).map g) ComplexShape.embeddingDownNat |>.f n)
      (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat |>.f n)
    rw [HomologicalComplex.extendMap_f _ _ hp, HomologicalComplex.extendMap_f _ _ hp,
      HomologicalComplex.extendMap_f _ _ hp, HomologicalComplex.extendMap_f _ _ hp]
    refine key.of_iso (HomologicalComplex.extendXIso ((chainsN R).obj (pullback f g)) _ hp).symm
      (HomologicalComplex.extendXIso ((chainsN R).obj E') _ hp).symm
      (HomologicalComplex.extendXIso ((chainsN R).obj U) _ hp).symm
      (HomologicalComplex.extendXIso ((chainsN R).obj E) _ hp).symm ?_ ?_ ?_ ?_ <;>
      exact (Iso.inv_hom_id_assoc _ _).symm
  · simp only [not_exists] at h
    have hz : ∀ X : Spc, IsZero (((chains R).obj X).X n) := fun X =>
      HomologicalComplex.isZero_extend_X ((chainsN R).obj X) ComplexShape.embeddingDownNat n h
    have := (hz _).isIso (hz _) (((chains R).map (pullback.snd f g)).f n)
    have := (hz _).isIso (hz _) (((chains R).map f).f n)
    exact IsPushout.of_horiz_isIso ⟨sq_comm R f g n⟩

abbrev PMod (R : Type) [CommRing R] : Type 2 := Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)

def LocOnto {R : Type} [CommRing R] {MB MC MD : PMod R} (c : MB ⟶ MD) (d : MC ⟶ MD) : Prop :=
  ∀ (T : Scheme.{0}) (z : MD.obj (op T)), EtLoc T fun V k =>
    ∃ (x : MB.obj (op V)) (y : MC.obj (op V)), (c.app (op V)).hom x + (d.app (op V)).hom y = (MD.map k.op).hom z

def LocKer {R : Type} [CommRing R] {MA MB MC MD : PMod R} (a : MA ⟶ MB) (b : MA ⟶ MC) (c : MB ⟶ MD) (d : MC ⟶ MD) :
    Prop :=
  ∀ (T : Scheme.{0}) (x : MB.obj (op T)) (y : MC.obj (op T)), (c.app (op T)).hom x + (d.app (op T)).hom y = 0 →
    EtLoc T fun V k => ∃ w : MA.obj (op V), (a.app (op V)).hom w = (MB.map k.op).hom x ∧
      (b.app (op V)).hom w = -(MC.map k.op).hom y

def LeafSheafPush : Prop := ∀ (R : Type) [CommRing R] {MA MB MC MD : PMod R} (a : MA ⟶ MB) (b : MA ⟶ MC)
  (c : MB ⟶ MD) (d : MC ⟶ MD), a ≫ c = b ≫ d → LocOnto c d → LocKer a b c d →
  IsPushout ((presheafToSheaf Scheme.etaleTopology.{0} _).map a) ((presheafToSheaf Scheme.etaleTopology.{0} _).map b) ((presheafToSheaf Scheme.etaleTopology.{0} _).map c)
    ((presheafToSheaf Scheme.etaleTopology.{0} _).map d)

def LeafFreeLoc : Prop := ∀ (R : Type) [CommRing R] {P U E' E : PSh} (fst : P ⟶ U) (snd : P ⟶ E') (f : U ⟶ E) [Mono f]
  (g : E' ⟶ E), IsPullback fst snd f g →
  (∀ (T : Scheme.{0}) (y : E.obj (op T)), EtLoc T fun V k =>
    (∃ u : U.obj (op V), f.app (op V) u = E.map k.op y) ∨ ∃ a : E'.obj (op V), g.app (op V) a = E.map k.op y) →
  (∀ (T : Scheme.{0}) (a b : E'.obj (op T)), g.app (op T) a = g.app (op T) b → EtLoc T fun V k =>
    E'.map k.op a = E'.map k.op b ∨ ∃ u : U.obj (op V), f.app (op V) u = E.map k.op (g.app (op T) a)) →
  LocOnto ((freeP R).map g) ((freeP R).map f) ∧
    LocKer ((freeP R).map snd) ((freeP R).map fst) ((freeP R).map g) ((freeP R).map f)

theorem LeafSqFree_of (hSP : LeafSheafPush) (hFL : LeafFreeLoc) : LeafSqFree := by
  intro R _ P U E' E fst snd f _ g hpb h1 h2
  obtain ⟨hon, hker⟩ := hFL R fst snd f g hpb h1 h2
  have hw : (freeP R).map snd ≫ (freeP R).map g = (freeP R).map fst ≫ (freeP R).map f := by
    rw [← Functor.map_comp, ← Functor.map_comp, hpb.w]
  exact hSP R _ _ _ _ hw hon hker

theorem square_of_pushout_and_free_local (hSP : LeafSheafPush) (hFL : LeafFreeLoc) : LeafSq := LeafSq_of (LeafSqFree_of hSP hFL)

end LateralTheory.E.LeafSqPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTermsPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafTermsPf

variable {R : Type} [CommRing R]

theorem HKpull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem HKpull_id (K : Cx R) (F : Shv R) (n : ℤ) (x : HK R K F n) : HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem finite_of_retract {K L : Cx R} (s : K ⟶ L) (t : L ⟶ K) (h : s ≫ t = 𝟙 K) (F : Shv R) (n : ℤ)
    (hL : Finite (HK R L F n)) : Finite (HK R K F n) :=
  Finite.of_surjective (HK.pull R s F n) (fun x =>
    ⟨HK.pull R t F n x, by rw [← HKpull_comp, h, HKpull_id]⟩)

theorem finite_of_iso {A B : Shv R} (e : A ≅ B) (F : Shv R) (n : ℤ)
    (hB : Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj B) F n)) :
    Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj A) F n) :=
  finite_of_retract _ _ (((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).mapIso e).hom_inv_id) F n hB

theorem d_const_zero (P : PSh) : ((chains R).obj (disc.obj P)).d (-1) 0 = 0 := by
  have h := HomologicalComplex.extend_d_eq ((chainsN R).obj (disc.obj P)) ComplexShape.embeddingDownNat
    (i := 1) (j := 0) (i' := -1) (j' := 0) rfl rfl
  change (((chainsN R).obj (disc.obj P)).extend ComplexShape.embeddingDownNat).d (-1) 0 = 0
  rw [h]
  have : ((chainsN R).obj (disc.obj P)).d 1 0 = 0 := by
    simp [chainsN, Fin.sum_univ_two, SimplicialObject.δ, disc]
    first
      | (erw [neg_one_smul, one_smul, add_neg_cancel])
      | (simp only [one_smul, neg_smul]; exact add_neg_cancel _)
      | abel
    all_goals rfl
  rw [this]; simp

def proj0 (P : PSh) : (chains R).obj (disc.obj P) ⟶
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj (((chains R).obj (disc.obj P)).X 0) :=
  HomologicalComplex.mkHomToSingle (𝟙 _) (fun i hi => by
    have : i = -1 := by simp at hi; omega
    subst this; rw [d_const_zero]; simp)

theorem etale_chain_complex_degree_zero_incl_proj_eq_id (P : PSh) : LateralTheory.E.LeafSSCut.incl0 ((chains R).obj (disc.obj P)) ≫ proj0 P = 𝟙 _ := by
  apply HomologicalComplex.to_single_hom_ext
  simp [LateralTheory.E.LeafSSCut.incl0, proj0]

theorem finite_single_of_H (Z : Scheme.{0}) (F : Shv R) (m : ℤ) (h : Finite (H R (sch.obj Z) F m)) :
    Finite (HK R ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj (yoneda.obj Z))) F m) :=
  finite_of_iso (chainsXIso R (disc.obj (yoneda.obj Z)) 0).symm F m
    (finite_of_retract _ _ (etale_chain_complex_degree_zero_incl_proj_eq_id (R := R) (yoneda.obj Z)) F m h)

section Geo
variable {Y X : Scheme.{0}} (f : Y ⟶ X)

abbrev W (n : ℕ) : Scheme.{0} := widePullback X (fun _ : Fin n => Y) (fun _ => f)

def toPb (n : ℕ) : W f (n + 1) ⟶ pullback (WidePullback.base (fun _ : Fin n => f)) f :=
  pullback.lift (WidePullback.lift (WidePullback.base _) (fun j => WidePullback.π _ j.succ) (by simp))
    (WidePullback.π _ 0) (by simp [WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_base, WidePullback.lift_base_assoc])

def ofPb (n : ℕ) : pullback (WidePullback.base (fun _ : Fin n => f)) f ⟶ W f (n + 1) :=
  WidePullback.lift (pullback.snd _ _ ≫ f)
    (Fin.cases (pullback.snd _ _) (fun j => pullback.fst _ _ ≫ WidePullback.π _ j))
    (by intro j; refine Fin.cases ?_ (fun j => ?_) j <;> simp [pullback.condition, WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_base, WidePullback.lift_base_assoc])

theorem toPb_ofPb (n : ℕ) : toPb f n ≫ ofPb f n = 𝟙 _ := by
  apply WidePullback.hom_ext
  · intro j
    simp only [Category.assoc, Category.id_comp]
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [ofPb, WidePullback.lift_π]; simp only [Fin.cases_zero]; rw [toPb, pullback.lift_snd]
    · rw [ofPb, WidePullback.lift_π]; simp only [Fin.cases_succ]
      rw [toPb, pullback.lift_fst_assoc, WidePullback.lift_π]
  · simp only [Category.assoc, Category.id_comp]
    rw [ofPb, WidePullback.lift_base, toPb, pullback.lift_snd_assoc, WidePullback.π_arrow]

theorem ofPb_toPb (n : ℕ) : ofPb f n ≫ toPb f n = 𝟙 _ := by
  apply pullback.hom_ext
  · apply WidePullback.hom_ext
    · intro j
      simp only [Category.assoc, Category.id_comp]
      rw [toPb, pullback.lift_fst_assoc, WidePullback.lift_π, ofPb, WidePullback.lift_π]
      simp only [Fin.cases_succ]
    · simp only [Category.assoc, Category.id_comp]
      rw [toPb, pullback.lift_fst_assoc, WidePullback.lift_base, ofPb, WidePullback.lift_base, pullback.condition]
  · simp only [Category.assoc, Category.id_comp]
    rw [toPb, pullback.lift_snd, ofPb, WidePullback.lift_π]
    simp only [Fin.cases_zero]

theorem base_zero_iso : IsIso (WidePullback.base (fun _ : Fin 0 => f)) :=
  ⟨⟨WidePullback.lift (𝟙 X) (fun j => j.elim0) (fun j => j.elim0), by
    refine ⟨WidePullback.hom_ext _ _ _ (fun j => j.elim0) (by simp [WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_base, WidePullback.lift_base_assoc]), by simp [WidePullback.lift_π, WidePullback.lift_π_assoc, WidePullback.lift_base, WidePullback.lift_base_assoc]⟩⟩⟩

theorem base_proper [IsProper f] : ∀ n : ℕ, IsProper (WidePullback.base (fun _ : Fin n => f))
  | 0 => by
    have := base_zero_iso f
    first | infer_instance | exact MorphismProperty.of_isIso (P := @IsProper) _
  | n + 1 => by
    have := base_proper n
    have hi : IsIso (toPb f n) := ⟨⟨ofPb f n, toPb_ofPb f n, ofPb_toPb f n⟩⟩
    have : WidePullback.base (fun _ : Fin (n + 1) => f) = toPb f n ≫ pullback.fst _ _ ≫ WidePullback.base _ := by
      rw [toPb, pullback.lift_fst_assoc, WidePullback.lift_base]
    rw [this]
    infer_instance

def eIso (n : ℕ) : yoneda.obj (W f n) ≅ widePullback (yoneda.obj X) (fun _ : Fin n => yoneda.obj Y) (fun _ => yoneda.map f) :=
  preservesLimitIso yoneda _ ≪≫ HasLimit.isoOfNatIso (WidePullbackShape.diagramIsoWideCospan _)

end Geo

theorem LeafTerms_of : LateralTheory.E.LeafSSCut.LeafTerms := by
  intro _ R _ F Y X f _ r m hZ
  refine finite_of_iso ((chainsXIso R (cech f) r) ≪≫ (free R).mapIso (eIso f (r + 1)).symm) F m ?_
  exact finite_single_of_H _ F m (hZ _ _ (base_proper f (r + 1)))

end LateralTheory.E.LeafTermsPf
end
end

