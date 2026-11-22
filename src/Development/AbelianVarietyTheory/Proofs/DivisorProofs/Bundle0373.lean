import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0019
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorSectionsLocallyBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceChainsMayerVietorisShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnity
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.PrimLoc
open Polynomial

lemma loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : ∀ V g, P V g → Q V g) (hP : Loc U P) : Loc U Q := by
  obtain ⟨S, hS, h1⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (h1 V g hg)⟩

lemma appTop_comp {V W U : Scheme.{0}} (g : V ⟶ U) (k : W ⟶ V) (a : Γ(U, ⊤)) :
    (k ≫ g).appTop.hom a = k.appTop.hom (g.appTop.hom a) := by
  rw [Scheme.Hom.comp_appTop]; rfl

lemma isUnit_prod' {R : Type*} [CommRing R] (S : Finset ℕ) (f : ℕ → R) (h : ∀ a ∈ S, IsUnit (f a)) :
    IsUnit (∏ a ∈ S, f a) := by
  exact IsUnit.prod_iff.mpr h

lemma loc_of_prod_eq_zero {U : Scheme.{0}} (y : Γ(U, ⊤)) (z : ℕ → Γ(U, ⊤)) (S : Finset ℕ)
    (hprod : ∏ a ∈ S, (y - z a) = 0) (hu : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → IsUnit (z a - z b)) :
    Loc U fun _ g => ∃ a ∈ S, g.appTop.hom y = g.appTop.hom (z a) := by
  classical
  rw [loc_iff_etale_affine_points U _ (by
    rintro V W g k ⟨a, ha, h⟩
    exact ⟨a, ha, by rw [appTop_comp, appTop_comp, h]⟩)]
  intro x
  let γ := (U.presheaf.germ ⊤ x trivial).hom
  have hex : ∃ a ∈ S, ¬ IsUnit (γ (y - z a)) := by
    by_contra hc
    push_neg at hc
    have h1 : IsUnit (γ (∏ a ∈ S, (y - z a))) := by
      rw [map_prod]; exact isUnit_prod' S _ hc
    rw [hprod, map_zero] at h1
    exact not_isUnit_zero h1
  obtain ⟨a0, ha0, hna⟩ := hex
  set s := ∏ b ∈ S.erase a0, (y - z b) with hs
  have hsu : IsUnit (γ s) := by
    rw [hs, map_prod]
    apply isUnit_prod'
    intro b hb
    obtain ⟨hba, hbS⟩ := Finset.mem_erase.1 hb
    by_contra hnb
    have hun : IsUnit (γ (z a0 - z b)) := (hu a0 ha0 b hbS (Ne.symm hba)).map γ
    have e : γ (z a0 - z b) = γ (y - z b) + -(γ (y - z a0)) := by
      rw [← map_neg, ← map_add]; congr 1; ring
    rw [e] at hun
    exact (IsLocalRing.nonunits_add ((mem_nonunits_iff).2 hnb)
      ((mem_nonunits_iff).2 (fun h => hna (by simpa using h.neg)))) hun
  have hxs : x ∈ U.basicOpen s := (Scheme.mem_basicOpen_top U s x).2 hsu
  let W := U.basicOpen s
  let xW : W.toScheme := ⟨x, hxs⟩
  obtain ⟨w, hw⟩ := W.toScheme.affineCover.covers xW
  refine ⟨_, W.toScheme.affineCover.f (W.toScheme.affineCover.idx xW) ≫ W.ι, inferInstance, inferInstance, ⟨w, ?_⟩, a0, ha0, ?_⟩
  · simp [hw, xW]
  · set k := W.toScheme.affineCover.f (W.toScheme.affineCover.idx xW)
    have hsW : IsUnit (W.ι.appTop.hom s) := by
      rw [Scheme.Opens.ι_appTop]
      have h0 : IsUnit ((U.presheaf.map (homOfLE (U.basicOpen_le s)).op).hom s) := U.toRingedSpace.isUnit_res_basicOpen s
      have hle : W.ι ''ᵁ ⊤ ≤ W := by
        rintro _ ⟨y, -, rfl⟩
        exact y.2
      have e : (homOfLE le_top : W.ι ''ᵁ ⊤ ⟶ ⊤) = homOfLE hle ≫ homOfLE (U.basicOpen_le s) := Subsingleton.elim _ _
      rw [e, op_comp, Functor.map_comp]
      exact h0.map (U.presheaf.map (homOfLE hle).op).hom
    have hk : IsUnit ((k ≫ W.ι).appTop.hom s) := by
      rw [appTop_comp]; exact hsW.map _
    have hm : (y - z a0) * s = 0 := by rw [hs, Finset.mul_prod_erase S (fun b => y - z b) ha0, hprod]
    have h2 := congrArg (k ≫ W.ι).appTop.hom hm
    rw [map_mul, map_zero, hk.mul_left_eq_zero, map_sub, sub_eq_zero] at h2
    exact h2

end GlobalTheory.EtC.PrimLoc

namespace GlobalTheory.EtC.PrimLoc
open Polynomial

lemma specMap_algebraMap_comp_apply_primeSpectrum {U : Scheme.{0}} {A : CommRingCat.{0}} {B : Type} [CommRing B] [Algebra A B] (f : Spec A ⟶ U)
    (z : PrimeSpectrum B) :
    (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ f) z = f (PrimeSpectrum.comap (algebraMap A B) z) := rfl

lemma loc_of_alg {U : Scheme.{0}} (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g))
    (h : ∀ (A : CommRingCat.{0}) (f : Spec A ⟶ U), Nontrivial A → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B),
      Algebra.Etale A B ∧ Function.Surjective (PrimeSpectrum.comap (algebraMap A B)) ∧
      P (Spec (CommRingCat.of B)) (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ f)) : Loc U P := by
  rw [loc_iff_etale_affine_points U P hP]
  intro x
  obtain ⟨y, hy⟩ := U.affineOpenCover.covers x
  have hA : Nontrivial (U.affineOpenCover.X (U.affineOpenCover.idx x)) :=
    nontrivial_of_ne 0 1 (fun h => y.2.ne_top ((Ideal.eq_top_iff_one _).2 (h ▸ y.asIdeal.zero_mem)))
  obtain ⟨B, _, _, hE, hS, hPB⟩ := h _ (U.affineOpenCover.f (U.affineOpenCover.idx x)) hA
  obtain ⟨z, hz⟩ := hS y
  haveI : Etale (Spec.map (CommRingCat.ofHom (algebraMap (U.affineOpenCover.X (U.affineOpenCover.idx x)) B))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr hE)
  refine ⟨_, _, inferInstance, inferInstance, ⟨z, ?_⟩, hPB⟩
  rw [specMap_algebraMap_comp_apply_primeSpectrum, hz, hy]

lemma adjoinRoot_surj {A : Type} [CommRing A] [Nontrivial A] (f : A[X]) (hf : f.Monic) (hd : f.natDegree ≠ 0) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (AdjoinRoot f))) := by
  haveI : Module.Free A (AdjoinRoot f) := Module.Free.of_basis (AdjoinRoot.powerBasis' hf).basis
  haveI : Nontrivial (AdjoinRoot f) := Ideal.Quotient.nontrivial_iff.mpr (by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro h
    exact hd (by rw [hf.isUnit_iff.1 h, natDegree_one]))
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

lemma etale_of_unit {A : Type} [CommRing A] (f : A[X]) (hm : f.Monic) (h : IsUnit (AdjoinRoot.mk f (derivative f))) :
    Algebra.Etale A (AdjoinRoot f) := by
  let P : StandardEtalePair A := ⟨f, hm, derivative f, 1, 0, 1, by simp⟩
  exact .of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit _ (Localization.Away (AdjoinRoot.mk f (derivative f))) _
      h).symm.restrictScalars A))

lemma cyc_etale {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    Algebra.Etale A (AdjoinRoot (cyclotomic q A)) := by
  apply etale_of_unit _ (cyclotomic.monic q A)
  obtain ⟨G, hG⟩ := cyclotomic.dvd_X_pow_sub_one q A
  have hx : AdjoinRoot.root (cyclotomic q A) ^ q = 1 := by
    have := congrArg (AdjoinRoot.mk (cyclotomic q A)) hG
    rw [map_mul, AdjoinRoot.mk_self, zero_mul, map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at this
    exact this
  have hd := congrArg (fun p => AdjoinRoot.mk (cyclotomic q A) (derivative p)) hG
  simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_one, sub_zero, map_add, map_mul,
    AdjoinRoot.mk_self, zero_mul, add_zero] at hd
  have hu : IsUnit (AdjoinRoot.mk (cyclotomic q A) (C (q : A)) * AdjoinRoot.mk (cyclotomic q A) (X ^ (q - 1))) := by
    rw [map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
    refine (hq.map _).mul (IsUnit.pow _ ?_)
    exact (isUnit_pow_iff (NeZero.ne q)).1 (hx ▸ isUnit_one)
  rw [hd] at hu
  exact isUnit_of_mul_isUnit_left hu

def cyc_root {A : Type} [CommRing A] (q : ℕ) (hq : IsUnit (q : A)) : Prim q (AdjoinRoot (cyclotomic q A)) :=
  ⟨AdjoinRoot.root _, by simpa using hq.map (algebraMap A (AdjoinRoot (cyclotomic q A))), by
    rw [PrimBasic.aeval_cyc, ← map_cyclotomic q (AdjoinRoot.of (cyclotomic q A)), Polynomial.eval_map]
    exact AdjoinRoot.eval₂_root _⟩

lemma kummer_root {A : Type} [CommRing A] (q : ℕ) (hq0 : q ≠ 0) (u : Aˣ) :
    ∃ v : (AdjoinRoot (X ^ q - C (u : A)))ˣ, (v : AdjoinRoot (X ^ q - C (u : A))) ^ q = algebraMap A _ u := by
  have h1 : AdjoinRoot.root (X ^ q - C (u : A)) ^ q = algebraMap A _ u := by
    have := AdjoinRoot.eval₂_root (X ^ q - C (u : A))
    simpa [sub_eq_zero] using this
  have hr : IsUnit (AdjoinRoot.root (X ^ q - C (u : A))) := (isUnit_pow_iff hq0).1 (h1 ▸ u.isUnit.map _)
  exact ⟨hr.unit, by simpa using h1⟩

lemma spec_appTop {A B : CommRingCat.{0}} (ψ : A ⟶ B) (t : Γ(Spec A, ⊤)) :
    (Spec.map ψ).appTop.hom t = (Scheme.ΓSpecIso B).inv.hom (ψ.hom ((Scheme.ΓSpecIso A).hom.hom t)) := by
  have e := congrArg (fun φ => φ.hom t) (Scheme.ΓSpecIso_naturality ψ)
  simp only [CommRingCat.comp_apply] at e
  rw [← e]
  simp

end GlobalTheory.EtC.PrimLoc

namespace GlobalTheory.EtC.PrimLoc
open Polynomial

theorem prim_loc : ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u) := by
  intro q _ U
  obtain ⟨-, -, h3, h4, h5, -⟩ := PrimBasic.prim_basic q Γ(U, ⊤)
  have hmod : ∀ a ∈ Finset.range q, ∀ b ∈ Finset.range q, a ≠ b → ¬ a ≡ b [MOD q] := by
    intro a ha b hb hab h
    apply hab
    unfold Nat.ModEq at h
    rwa [Nat.mod_eq_of_lt (Finset.mem_range.1 ha), Nat.mod_eq_of_lt (Finset.mem_range.1 hb)] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hq
    refine loc_of_alg (fun V _ => Nonempty (Prim q Γ(V, ⊤))) (fun V W g k ⟨ζ⟩ => ⟨ζ.map k.appTop.hom⟩) ?_
    intro A f hA
    have hqA : IsUnit (q : A) := by
      simpa using hq.map (f.appTop ≫ (Scheme.ΓSpecIso A).hom).hom
    refine ⟨AdjoinRoot (cyclotomic q A), inferInstance, inferInstance, cyc_etale q hqA,
      adjoinRoot_surj _ (cyclotomic.monic q A) ?_, ⟨(cyc_root q hqA).map (Scheme.ΓSpecIso _).inv.hom⟩⟩
    rw [natDegree_cyclotomic]
    exact (Nat.totient_pos.2 (NeZero.pos q)).ne'
  · intro ζ ξ
    refine loc_mono ?_ (loc_of_prod_eq_zero ξ.1 (fun a => ζ.1 ^ a) _ (h5 ζ ξ) ?_)
    · rintro V g ⟨a, ha, h⟩
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
      refine ⟨ZMod.unitOfCoprime a ha2, ?_⟩
      rw [h, map_pow, ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 ha1)]
    · intro a ha b hb hab
      exact h3 ζ a b (hmod a (Finset.mem_filter.1 ha).1 b (Finset.mem_filter.1 hb).1 hab)
  · intro ζ x hx
    refine loc_mono ?_ (loc_of_prod_eq_zero x (fun a => ζ.1 ^ a) _ (h4 ζ x hx) ?_)
    · rintro V g ⟨a, -, h⟩
      exact ⟨a, by rw [h, map_pow]⟩
    · intro a ha b hb hab
      exact h3 ζ a b (hmod a ha b hb hab)
  · intro hq u
    refine loc_of_alg (fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u) ?_ ?_
    · rintro V W g k ⟨v, hv⟩
      refine ⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩
      rw [← map_pow, hv]
      ext
      rfl
    intro A f hA
    have hqA : IsUnit (q : A) := by
      simpa using hq.map (f.appTop ≫ (Scheme.ΓSpecIso A).hom).hom
    obtain ⟨uA, huA⟩ : ∃ uA : (A : Type)ˣ, uA = Units.map (f.appTop ≫ (Scheme.ΓSpecIso A).hom).hom.toMonoidHom u :=
      ⟨_, rfl⟩
    obtain ⟨v, hv⟩ := kummer_root q (NeZero.ne q) uA
    refine ⟨AdjoinRoot (X ^ q - C (uA : A)), inferInstance, inferInstance,
      GlobalTheory.etale_adjoinRoot_X_pow_sub_C A q uA hqA uA.isUnit,
      adjoinRoot_surj _ (monic_X_pow_sub_C _ (NeZero.ne q)) ?_,
      ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot (X ^ q - C (uA : A))))).inv.hom.toMonoidHom v, ?_⟩⟩
    · rw [natDegree_X_pow_sub_C]
      exact NeZero.ne q
    · ext
      have hu' : (uA : A) = (Scheme.ΓSpecIso A).hom.hom (f.appTop.hom (u : Γ(U, ⊤))) := by rw [huA]; rfl
      rw [Units.val_pow_eq_pow_val, Units.coe_map, Units.coe_map]
      show (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot (X ^ q - C (uA : A))))).inv.hom (v : AdjoinRoot (X ^ q - C (uA : A))) ^ q =
        (Spec.map (CommRingCat.ofHom (algebraMap A (AdjoinRoot (X ^ q - C (uA : A))))) ≫ f).appTop.hom (u : Γ(U, ⊤))
      rw [appTop_comp, spec_appTop, ← map_pow, hv]
      congr 1
      exact congrArg (algebraMap A (AdjoinRoot (X ^ q - C (uA : A)))) hu'

end GlobalTheory.EtC.PrimLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafComplexMappingConeAcyclicOfQuasiIsoStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafComplex_mappingCone_acyclic_of_quasiIso : ∀ (R : Type) [CommRing R] {C J : Cx R} (u : C ⟶ J) [QuasiIso u], (mappingCone u).Acyclic := by
  first | exact @GlobalTheory.EtC.mappingCone_acyclic | exact GlobalTheory.EtC.mappingCone_acyclic | (intros; apply GlobalTheory.EtC.mappingCone_acyclic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafDescendAlongLocallyBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

namespace DescLoc

variable {S : Type} [CommRing S] {P Q : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}} (φ : P ⟶ Q)

theorem res_res {M : Shv S} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec M U) :
    Sec.res k (Sec.res g a) = Sec.res (k ≫ g) a := by
  simp [Sec.res]

theorem res_add {M : Shv S} {V U : Scheme.{0}} (g : V ⟶ U) (a a' : Sec M U) :
    Sec.res g (a + a') = Sec.res g a + Sec.res g a' := map_add _ _ _

theorem pmap_comp (P : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}) {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U)
    (x : P.obj (op U)) : (P.map k.op).hom ((P.map g.op).hom x) = (P.map (k ≫ g).op).hom x := by
  simp

theorem nat_apply {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (φ.app (op V)).hom ((P.map g.op).hom x) = (Q.map g.op).hom ((φ.app (op U)).hom x) := by
  have := congrArg (fun f => f.hom x) (φ.naturality g.op)
  simpa using this

section Main
variable {S : Type} [CommRing S] {P Q : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}} (φ : P ⟶ Q) (M : Shv S)
  (b : ∀ U : Scheme.{0}, P.obj (op U) →+ Sec M U)
  (hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V ((P.map g.op).hom x))

theorem ext_loc {U : Scheme.{0}} (a a' : Sec M U) (h : Loc U fun _ g => Sec.res g a = Sec.res g a') : a = a' :=
  (sec_ext_glue S M U).1 a a' h

include hb in

theorem key (h2 : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)
    {V : Scheme.{0}} (x x' : P.obj (op V)) (hx : (φ.app (op V)).hom x = (φ.app (op V)).hom x') : b V x = b V x' := by
  obtain ⟨T, hT, hz⟩ := h2 V (x - x') (by rw [map_sub, hx, sub_self])
  refine ext_loc M _ _ ⟨T, hT, fun W k hk => ?_⟩
  dsimp only
  rw [hb, hb]
  have := hz W k hk
  dsimp only at this
  rw [map_sub, sub_eq_zero] at this
  rw [this]

def Ch (U : Scheme.{0}) (y : Q.obj (op U)) (a : Sec M U) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U) (x : P.obj (op V)), (φ.app (op V)).hom x = (Q.map g.op).hom y → Sec.res g a = b V x

theorem ch_unique (h1 : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
    {U : Scheme.{0}} (y : Q.obj (op U)) (a a' : Sec M U) (ha : Ch φ M b U y a) (ha' : Ch φ M b U y a') : a = a' := by
  obtain ⟨T, hT, hl⟩ := h1 U y
  refine ext_loc M _ _ ⟨T, hT, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hl V g hg
  rw [ha V g x hx, ha' V g x hx]

include hb in
theorem ch_exists (h1 : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
    (h2 : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)
    (U : Scheme.{0}) (y : Q.obj (op U)) : ∃ a, Ch φ M b U y a := by
  obtain ⟨T, hT, hl⟩ := h1 U y
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ U), T.arrows g → Sec M V := fun V g hg => b V (hl V g hg).choose
  have hs : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : T.arrows g),
      Sec.res k (s V g hg) = s W (k ≫ g) (T.downward_closed hg k) := by
    intro V W g k hg
    simp only [s]
    rw [hb]
    apply key φ M b hb h2
    rw [nat_apply, (hl V g hg).choose_spec, (hl W (k ≫ g) (T.downward_closed hg k)).choose_spec, pmap_comp]
  obtain ⟨a, ha⟩ := (sec_ext_glue S M U).2 T hT s hs
  refine ⟨a, fun V g x hx => ?_⟩
  refine ext_loc M _ _ ⟨T.pullback g, Scheme.etaleTopology.pullback_stable g hT, fun W k hk => ?_⟩
  dsimp only
  rw [res_res, ha W (k ≫ g) hk, hb]
  simp only [s]
  apply key φ M b hb h2
  rw [nat_apply, hx, (hl W (k ≫ g) hk).choose_spec, pmap_comp]

end Main

section Main2
variable {S : Type} [CommRing S] {P Q : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}} (φ : P ⟶ Q) (M : Shv S)
  (b : ∀ U : Scheme.{0}, P.obj (op U) →+ Sec M U)
  (hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V ((P.map g.op).hom x))
  (h1 : ∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y)
  (h2 : ∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0)

include hb h1 h2 in
theorem ch_add {U : Scheme.{0}} (y y' : Q.obj (op U)) (a a' : Sec M U) (ha : Ch φ M b U y a) (ha' : Ch φ M b U y' a') :
    Ch φ M b U (y + y') (a + a') := by
  intro V g x hx
  obtain ⟨T1, hT1, hl1⟩ := h1 V ((Q.map g.op).hom y)
  obtain ⟨T2, hT2, hl2⟩ := h1 V ((Q.map g.op).hom y')
  refine ext_loc M _ _ ⟨T1 ⊓ T2, Scheme.etaleTopology.intersection_covering hT1 hT2, fun W k hk => ?_⟩
  obtain ⟨x1, e1⟩ := hl1 W k hk.1
  obtain ⟨x2, e2⟩ := hl2 W k hk.2
  rw [pmap_comp] at e1 e2
  rw [res_res, res_add, ha W (k ≫ g) x1 e1, ha' W (k ≫ g) x2 e2, hb, ← map_add]
  apply key φ M b hb h2
  rw [nat_apply, hx, pmap_comp]
  simp only [map_add, e1, e2]

theorem ch_res {U V : Scheme.{0}} (h : V ⟶ U) (y : Q.obj (op U)) (a : Sec M U) (ha : Ch φ M b U y a) :
    Ch φ M b V ((Q.map h.op).hom y) (Sec.res h a) := by
  intro W k x hx
  rw [res_res]
  exact ha W (k ≫ h) x (by rw [hx, pmap_comp])

include hb h2 in
theorem ch_base {U : Scheme.{0}} (x : P.obj (op U)) : Ch φ M b U ((φ.app (op U)).hom x) (b U x) := by
  intro V g x' hx
  rw [hb]
  apply key φ M b hb h2
  rw [nat_apply, hx]

end Main2
end DescLoc

open DescLoc in
theorem desc_loc : ∀ (S : Type) [CommRing S] (P Q : Scheme.{0}ᵒᵖ ⥤ AddCommGrpCat.{1}) (φ : P ⟶ Q), (∀ (U : Scheme.{0}) (y : Q.obj (op U)), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = (Q.map g.op).hom y) → (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) → ∀ (M : Shv S) (b : ∀ U : Scheme.{0}, P.obj (op U) →+ Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) x, Sec.res g (b U x) = b V ((P.map g.op).hom x)) → ∃ c : ∀ U : Scheme.{0}, Q.obj (op U) →+ Sec M U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (c U y) = c V ((Q.map g.op).hom y)) ∧ ∀ U x, c U ((φ.app (op U)).hom x) = b U x := by
  intro S _ P Q φ h1 h2 M b hb
  have hex := ch_exists φ M b hb h1 h2
  let c0 : ∀ U : Scheme.{0}, Q.obj (op U) → Sec M U := fun U y => (hex U y).choose
  have hc0 : ∀ U y, Ch φ M b U y (c0 U y) := fun U y => (hex U y).choose_spec
  let c : ∀ U : Scheme.{0}, Q.obj (op U) →+ Sec M U := fun U =>
    AddMonoidHom.mk' (c0 U) (fun y y' => ch_unique φ M b h1 (y + y') _ _ (hc0 U (y + y'))
      (ch_add φ M b hb h1 h2 y y' _ _ (hc0 U y) (hc0 U y')))
  refine ⟨c, fun V U g y => ?_, fun U x => ?_⟩
  · exact ch_unique φ M b h1 _ _ _ (ch_res φ M b g y _ (hc0 U y)) (hc0 V _)
  · exact ch_unique φ M b h1 _ _ _ (hc0 U _) (ch_base φ M b hb h2 x)
end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorSectionsLocallyBijectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafOfRingFunctor_sections_locally_bijective : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0}), (∀ (x : Sec (ofRings R M) U) (u : U), ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V) (m : M.obj Γ(V, ⊤)), IsAffine V ∧ Etale j ∧ j v = u ∧ ofRings.sec M V m = Sec.res j x) ∧ (∀ m : M.obj Γ(U, ⊤), ofRings.sec M U m = 0 → ∀ u : U, ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), IsAffine V ∧ Etale j ∧ j v = u ∧ (M.map j.appTop).hom m = 0) ∧ ∀ (V : Scheme.{0}) (j : V ⟶ U) (m : M.obj Γ(U, ⊤)), Sec.res j (ofRings.sec M U m) = ofRings.sec M V ((M.map j.appTop).hom m) := by
  first | (exact @GlobalTheory.ofRings_loc) | (exact GlobalTheory.ofRings_loc) | (intros; apply GlobalTheory.ofRings_loc  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafSections_ext_and_glue : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}), (∀ a b : Sec F U, (Loc U fun _ g => Sec.res g a = Sec.res g b) → a = b) ∧ ∀ (S : Sieve U), S ∈ Scheme.etaleTopology U → ∀ s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec F V, (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g), Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k)) → ∃ a : Sec F U, ∀ V g hg, Sec.res g a = s V g hg := by
  first | exact @GlobalTheory.EtC.sec_ext_glue | exact GlobalTheory.EtC.sec_ext_glue | (intros; apply GlobalTheory.EtC.sec_ext_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsGlueOfLocallyUniqueStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafSections_glue_of_locally_unique : ∀ {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0}) (A : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U → Prop),
    (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), A U x s → A V (g ≫ x) (Sec.res g s)) →
    (∀ (U : Scheme.{0}) (x : U ⟶ X) (s t : Sec F U), A U x s → A U x t → s = t) →
    (∀ (U : Scheme.{0}) (x : U ⟶ X), Loc U fun V g => ∃ s, A V (g ≫ x) s) →
    ∃ e : ∀ U : Scheme.{0}, (U ⟶ X) → Sec F U, (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : U ⟶ X), Sec.res g (e U x) = e V (g ≫ x)) ∧
      ∀ (U : Scheme.{0}) (x : U ⟶ X) (s : Sec F U), A U x s → e U x = s := by
  first | exact @GlobalTheory.EtC.secGlue_of_loc | exact GlobalTheory.EtC.secGlue_of_loc | (intros; apply GlobalTheory.EtC.secGlue_of_loc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsSepGlueOfSurjectiveFamilyStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafSections_sep_glue_of_surjective_family : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), (∀ i, Etale (j i)) → (∀ u : U, ∃ i v, j i v = u) → (∀ x : Sec F U, (∀ i, Sec.res (j i) x = 0) → x = 0) ∧ ∀ y : ∀ i, Sec F (V i), (∀ i k, Sec.res (pullback.fst (j i) (j k)) (y i) = Sec.res (pullback.snd (j i) (j k)) (y k)) → ∃ x : Sec F U, ∀ i, Sec.res (j i) x = y i := by
  first | exact @GlobalTheory.EtC.sec_sep_glue_of_points | exact GlobalTheory.EtC.sec_sep_glue_of_points | (intros; apply GlobalTheory.EtC.sec_sep_glue_of_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceChainsMayerVietorisShortExactStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpaceChains_mayerVietoris_shortExact : ∀ (R : Type) [CommRing R] {U V E : Spc} (f : U ⟶ E) (g : V ⟶ E), Cover2 R f g → ∃ w, (ShortComplex.mk (biprod.lift ((chains R).map (pullback.fst f g)) (-(chains R).map (pullback.snd f g))) (biprod.desc ((chains R).map f) ((chains R).map g)) w).ShortExact := by
  first | (exact @GlobalTheory.EtC.mv_shortExact) | (exact GlobalTheory.EtC.mv_shortExact) | (intros; apply GlobalTheory.EtC.mv_shortExact  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceSimplicesOverSubCompositeStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite : ∀ {E : Spc} {U : Scheme.{0}} {N : ℕ} (x : Sx E N U), (∀ (j l j' l' : ℕ) (h : j + l ≤ N) (h' : j' + l' ≤ l), (x.sub j l h).sub j' l' h' = x.sub (j + j') l' (by omega)) ∧ x.sub 0 N (by omega) = x ∧ (∀ (j l : ℕ) (h : j + l ≤ N), (∀ {V : Scheme.{0}} (g : V ⟶ U), (x.res g).sub j l h = (x.sub j l h).res g) ∧ (∀ {E' : Spc} (f : E ⟶ E'), (x.map f).sub j l h = (x.sub j l h).map f) ∧ x.sub j l h = x.along (SimplexCategory.subinterval j l h)) ∧ ∀ {p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk p), (x.along a).along b = x.along (b ≫ a) := by
  first | (exact @GlobalTheory.EtC.SubSub.main) | (exact GlobalTheory.EtC.SubSub.main) | (intros; apply GlobalTheory.EtC.SubSub.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleTensorDiagonalComplementOverBasicOpenStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_tensor_diagonal_complement_over_basicOpen : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) → (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) → ∃ e u : A' ⊗[A] A', (∀ a : A', (a ⊗ₜ[A] (1 : A') - (1 : A') ⊗ₜ[A] a) * e = 0) ∧ algebraMap A (A' ⊗[A] A') f * u = 1 - e := by
  first | (exact @GlobalTheory.etale_diag_complement) | (exact GlobalTheory.etale_diag_complement) | (intros; apply GlobalTheory.etale_diag_complement  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleToSheafify_locally_bijective_and_lift : ∀ (R : Type) [CommRing R] (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)), (∀ (U : Scheme.{0}) (y : Sec ((presheafToSheaf Scheme.etaleTopology _).obj P) U), Loc U fun V g => ∃ x, ((toSheafify Scheme.etaleTopology P).app (op V)).hom x = Sec.res g y) ∧ (∀ (U : Scheme.{0}) (x : P.obj (op U)), ((toSheafify Scheme.etaleTopology P).app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) ∧ ∀ (F : Shv R) (φ : P ⟶ F.obj), ∃! ψ : (presheafToSheaf Scheme.etaleTopology _).obj P ⟶ F, toSheafify Scheme.etaleTopology P ≫ ψ.hom = φ := by
  first | (exact @GlobalTheory.EtC.toSheafify_loc_bij_lift) | (exact GlobalTheory.EtC.toSheafify_loc_bij_lift) | (intros; apply GlobalTheory.EtC.toSheafify_loc_bij_lift  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineHilbertChartBasicNeighbourhoodStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineHilbertChartBasic_neighbourhood : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (z : Z), ∃ (σ : Fin r ↪ Fin N) (U : Z.Opens), z ∈ U ∧ GlobalTheory.HilbAff.Basic A B e σ ((GlobalTheory.HilbAff.functor A B r).map U.ι.op y) := by
  first | (exact @GlobalTheory.HilbAff.exists_basic_nhd) | (exact GlobalTheory.HilbAff.exists_basic_nhd) | (intros; apply GlobalTheory.HilbAff.exists_basic_nhd  <;> assumption)
end

