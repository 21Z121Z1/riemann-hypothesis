import Mathlib
import ReciprocityTheory.NeutralLocalFields.Reciprocity
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.UnipotentAdelicQuotients.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import GroundTheory.AutomorphicForms.GKModules.SmoothVectors
import GroundTheory.AutomorphicForms.GKModules.Bundle0001
import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DegOneIffSurjective
section
noncomputable section

namespace GlobalTheory.HeckeSplit

open NumberField IsDedekindDomain HeckeValGen

variable (L : Type) [Field L] [NumberField L]

def IsHeckeChar (χ : Ideles L →* ℂˣ) : Prop := Continuous χ ∧ ∀ k : Lˣ, χ (diagUnits L k) = 1

def infIdele : (InfiniteAdeleRing L)ˣ →* Ideles L :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

def infPart : Ideles L →* (InfiniteAdeleRing L)ˣ :=
  Units.map (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

def finPart (v : HeightOneSpectrum (𝓞 L)) : Ideles L →* (v.adicCompletion L)ˣ :=
  Units.map
    { toFun := fun x : AdeleRing (𝓞 L) L => (x.2 : FiniteAdeleRing (𝓞 L) L) v
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

variable {L}

def TrivAt (χ : Ideles L →* ℂˣ) (v : HeightOneSpectrum (𝓞 L)) : Prop :=
  ∀ x : (v.adicCompletion L)ˣ, χ (localIdele L v x) = 1

def UnrAt (χ : Ideles L →* ℂˣ) (v : HeightOneSpectrum (𝓞 L)) : Prop :=
  ∀ x : (v.adicCompletion L)ˣ, Valued.v (x : v.adicCompletion L) = 1 → χ (localIdele L v x) = 1

def DegOne (F : Type) [Field F] [NumberField F] [Algebra F L] (w : HeightOneSpectrum (𝓞 L)) : Prop :=
  ∀ y : 𝓞 L, ∃ u : 𝓞 F, y - algebraMap (𝓞 F) (𝓞 L) u ∈ w.asIdeal

variable (L)

open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in

theorem _root_.GlobalTheory.HeckeSplit.unrAt_iff (χ : _root_.Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    _root_.GlobalTheory.HeckeSplit.UnrAt χ.1 v ↔ χ.UnrAt v := by
  unfold _root_.GlobalTheory.HeckeSplit.UnrAt _root_.Formalism.L2.Host.HChar.UnrAt _root_.Formalism.L2.Host.IsUnitAt _root_.Formalism.L2.Host.HChar.loc
  rfl

open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in

theorem _root_.GlobalTheory.HeckeSplit.trivAt_iff (χ : _root_.Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    _root_.GlobalTheory.HeckeSplit.TrivAt χ.1 v ↔ χ.loc v = 1 := by
  unfold _root_.GlobalTheory.HeckeSplit.TrivAt
  rw [DFunLike.ext_iff]
  unfold _root_.Formalism.L2.Host.HChar.loc
  rfl

open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in

@[simp] theorem _root_.GlobalTheory.HeckeSplit.infPart_infIdele (x : (InfiniteAdeleRing L)ˣ) :
    _root_.GlobalTheory.HeckeSplit.infPart L (_root_.GlobalTheory.HeckeSplit.infIdele L x) = x :=
  Units.ext rfl

open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in

@[simp] theorem _root_.GlobalTheory.HeckeSplit.finPart_infIdele (v : HeightOneSpectrum (𝓞 L))
    (x : (InfiniteAdeleRing L)ˣ) :
    _root_.GlobalTheory.HeckeSplit.finPart L v (_root_.GlobalTheory.HeckeSplit.infIdele L x) = 1 :=
  Units.ext rfl

open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in

@[simp] theorem _root_.GlobalTheory.HeckeSplit.finPart_localIdele (v : HeightOneSpectrum (𝓞 L))
    (x : (v.adicCompletion L)ˣ) :
    _root_.GlobalTheory.HeckeSplit.finPart L v (_root_.HeckeValGen.localIdele L v x) = x :=
  Units.ext (_root_.Neutral.B1.localIdele_snd_self L v x)

open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in

@[simp] theorem _root_.GlobalTheory.HeckeSplit.infPart_localIdele (v : HeightOneSpectrum (𝓞 L))
    (x : (v.adicCompletion L)ˣ) :
    _root_.GlobalTheory.HeckeSplit.infPart L (_root_.HeckeValGen.localIdele L v x) = 1 :=
  Units.ext rfl

open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in

theorem _root_.GlobalTheory.HeckeSplit.finPart_localIdele_ne {v w : HeightOneSpectrum (𝓞 L)} (h : w ≠ v)
    (x : (v.adicCompletion L)ˣ) : _root_.GlobalTheory.HeckeSplit.finPart L w (_root_.HeckeValGen.localIdele L v x) = 1 :=
  Units.ext ((_root_.Neutral.B1.localIdele_isSupportedAt L v x).2 w h)

variable {L}

theorem IsHeckeChar.mul {χ ψ : Ideles L →* ℂˣ} (hχ : IsHeckeChar L χ) (hψ : IsHeckeChar L ψ) :
    IsHeckeChar L (χ * ψ) := (Formalism.L2.Host.hcharSub L).mul_mem hχ hψ

theorem IsHeckeChar.inv {χ : Ideles L →* ℂˣ} (hχ : IsHeckeChar L χ) :
    IsHeckeChar L χ⁻¹ := (Formalism.L2.Host.hcharSub L).inv_mem hχ

theorem TrivAt.unrAt {χ : Ideles L →* ℂˣ} {v : HeightOneSpectrum (𝓞 L)} (h : TrivAt χ v) :
    UnrAt χ v := fun x _ => h x

end GlobalTheory.HeckeSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsZeroFreeSchOfIsEmpty
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC.Tr

section Transfer

variable (R : Type) [CommRing R]

abbrev freeSch (X : Scheme.{0}) : Shv R := (free R).obj (yoneda.obj X)

def IsTransfer {Z X : Scheme.{0}} (f : Z ⟶ X) (t : freeSch R X ⟶ freeSch R Z) : Prop :=
  ∀ (S : Scheme.{0}) (x : S ⟶ X) (m : ℕ) (s : Fin m → (S ⟶ Z)) (hs : ∀ j, s j ≫ f = x),
    IsIso (Sigma.desc (fun j => pullback.lift (s j) (𝟙 S) (by rw [hs j, Category.id_comp])) :
      ∐ (fun _ : Fin m => S) ⟶ pullback f x) →
    (free R).map (yoneda.map x) ≫ t = ∑ j, (free R).map (yoneda.map (s j))

def transfer {Z X : Scheme.{0}} (f : Z ⟶ X) : freeSch R X ⟶ freeSch R Z := pick (IsTransfer R f)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable (R : Type) [CommRing R] in
theorem _root_.GlobalTheory.EtC.Tr.transfer_spec {Z X : Scheme.{0}} {f : Z ⟶ X}
    (h : ∃ t, _root_.GlobalTheory.EtC.Tr.IsTransfer R f t) :
    _root_.GlobalTheory.EtC.Tr.IsTransfer R f (_root_.GlobalTheory.EtC.Tr.transfer R f) :=
  _root_.GlobalTheory.EtC.pick_spec h

theorem isZero_freeSch_of_isEmpty (X : Scheme.{0}) [IsEmpty X] : IsZero (freeSch R X) := by
  rw [IsZero.iff_id_eq_zero]
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv
    ((freeP R).obj (yoneda.obj X)) (freeSch R X)).injective
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases isEmpty_or_nonempty U.unop with hU | hU
  · have hb : (⊥ : Sieve U.unop) ∈ Scheme.etaleTopology U.unop := Scheme.bot_mem_grothendieckTopology U.unop
    exact Sheaf.isSeparated (freeSch R X) U.unop ⊥ hb _ _ (fun _ _ h => h.elim)
  · have : IsEmpty (ULift.{1} (U.unop ⟶ X)) :=
      ⟨fun f => IsEmpty.false (f.down.base (Classical.arbitrary U.unop))⟩
    have hs : Subsingleton (ULift.{1} (U.unop ⟶ X) →₀ ULift.{1} R) := inferInstance
    have hx : x = 0 := hs.elim x 0
    subst hx
    simp

theorem eq_one_of_isIso_codiag {S : Scheme.{0}} (pt : S) {m : ℕ}
    (h : IsIso (Sigma.desc (fun _ : Fin m => 𝟙 S) : ∐ (fun _ : Fin m => S) ⟶ S)) : m = 1 := by
  rcases Nat.lt_trichotomy m 1 with hm | hm | hm
  · have hm0 : m = 0 := by omega
    subst hm0
    have f : S ⟶ (∅ : Scheme.{0}) :=
      inv (Sigma.desc (fun _ : Fin 0 => 𝟙 S)) ≫ Sigma.desc (fun j : Fin 0 => j.elim0)
    exact (IsEmpty.false (f pt)).elim
  · exact hm
  · exfalso
    let i : Fin m := ⟨0, by omega⟩
    let j : Fin m := ⟨1, hm⟩
    have hij : Sigma.ι (fun _ : Fin m => S) i = Sigma.ι (fun _ : Fin m => S) j :=
      (cancel_mono (Sigma.desc (fun _ : Fin m => 𝟙 S))).1 (by simp)
    have hp : Sigma.ι (fun _ : Fin m => S) i pt = Sigma.ι (fun _ : Fin m => S) j pt := by rw [hij]
    have := congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : Fin m => S) i j pt pt).mp hp)
    simp [i, j] at this

theorem isTransfer_id (X : Scheme.{0}) : IsTransfer R (𝟙 X) (𝟙 _) := by
  intro S x m s hs hiso
  have hsx : ∀ j, s j = x := fun j => by simpa using hs j
  simp only [Category.comp_id, hsx, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rcases isEmpty_or_nonempty S with hS | hS
  · exact (isZero_freeSch_of_isEmpty R S).eq_of_src _ _
  · obtain ⟨pt⟩ := hS
    have hc : (Sigma.desc (fun j => pullback.lift (s j) (𝟙 S) (by rw [hs j, Category.id_comp])) :
        ∐ (fun _ : Fin m => S) ⟶ pullback (𝟙 X) x) ≫ pullback.snd _ _ = Sigma.desc (fun _ : Fin m => 𝟙 S) := by
      apply Sigma.hom_ext; intro j; rw [Sigma.ι_desc_assoc, Sigma.ι_desc]; exact pullback.lift_snd _ _ _
    have : IsIso (Sigma.desc (fun _ : Fin m => 𝟙 S) : ∐ (fun _ : Fin m => S) ⟶ S) := by
      rw [← hc]; infer_instance
    rw [eq_one_of_isIso_codiag pt this, one_smul]

theorem eq_id_of_isTransfer_id {X : Scheme.{0}} {t : freeSch R X ⟶ freeSch R X} (ht : IsTransfer R (𝟙 X) t) : t = 𝟙 _ := by
  have hcod : IsIso (Sigma.desc (fun _ : Fin 1 => 𝟙 X) : ∐ (fun _ : Fin 1 => X) ⟶ X) :=
    ⟨⟨Sigma.ι (fun _ : Fin 1 => X) 0, by ext j; fin_cases j; simp, by simp⟩⟩
  have hc : (Sigma.desc (fun _ : Fin 1 => pullback.lift (𝟙 X) (𝟙 X) (by simp)) :
      ∐ (fun _ : Fin 1 => X) ⟶ pullback (𝟙 X) (𝟙 X)) ≫ pullback.snd _ _ = Sigma.desc (fun _ : Fin 1 => 𝟙 X) := by
    apply Sigma.hom_ext; intro j; rw [Sigma.ι_desc_assoc, Sigma.ι_desc]; exact pullback.lift_snd _ _ _
  have hiso : IsIso (Sigma.desc (fun _ : Fin 1 => pullback.lift (𝟙 X) (𝟙 X) (by simp)) :
      ∐ (fun _ : Fin 1 => X) ⟶ pullback (𝟙 X) (𝟙 X)) := by
    rw [← hc] at hcod
    exact IsIso.of_isIso_comp_right _ (pullback.snd (𝟙 X) (𝟙 X))
  have := ht X (𝟙 X) 1 (fun _ => 𝟙 X) (fun _ => by simp) hiso
  simpa using this

theorem transfer_id (X : Scheme.{0}) : transfer R (𝟙 X) = 𝟙 _ :=
  eq_id_of_isTransfer_id R (transfer_spec R ⟨_, isTransfer_id R X⟩)

end Transfer

section Trace

variable (R : Type) [CommRing R]

def simpMap {X Z : Scheme.{0}} (t : freeSch R X ⟶ freeSch R Z) :
    ((SimplicialObject.whiskering _ _).obj (free R)).obj (sch.obj X) ⟶
      ((SimplicialObject.whiskering _ _).obj (free R)).obj (sch.obj Z) where
  app _ := t
  naturality _ _ _ := by
    show (free R).map (𝟙 (yoneda.obj X)) ≫ t = t ≫ (free R).map (𝟙 (yoneda.obj Z))
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

def chainMap {X Z : Scheme.{0}} (t : freeSch R X ⟶ freeSch R Z) : (chains R).obj (sch.obj X) ⟶ (chains R).obj (sch.obj Z) :=
  (ComplexShape.embeddingDownNat.extendFunctor (Shv R)).map ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (simpMap R t))

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable (R : Type) [CommRing R] in

lemma _root_.GlobalTheory.EtC.Tr.chainMap_free {X Z : Scheme.{0}} (g : X ⟶ Z) :
    _root_.GlobalTheory.EtC.Tr.chainMap R ((_root_.GlobalTheory.EtC.free R).map (yoneda.map g)) =
      (_root_.GlobalTheory.EtC.chains R).map (_root_.GlobalTheory.EtC.sch.map g) := by
  have hsimp : _root_.GlobalTheory.EtC.Tr.simpMap R ((_root_.GlobalTheory.EtC.free R).map (yoneda.map g)) =
      ((SimplicialObject.whiskering _ _).obj (_root_.GlobalTheory.EtC.free R)).map
        (_root_.GlobalTheory.EtC.sch.map g) := by
    ext
    rfl
  unfold _root_.GlobalTheory.EtC.Tr.chainMap
  rw [hsimp]
  rfl

def along {X Z : Scheme.{0}} (F : Shv R) (n : ℤ) (t : freeSch R X ⟶ freeSch R Z) : H R (sch.obj Z) F n →+ H R (sch.obj X) F n :=
  HK.pull R (chainMap R t) F n

def alongL {X Z : Scheme.{0}} (F : Shv R) (n : ℤ) (t : freeSch R X ⟶ freeSch R Z) : H R (sch.obj Z) F n →ₗ[R] H R (sch.obj X) F n where
  toFun := along R F n t
  map_add' := map_add _
  map_smul' r x := by
    obtain ⟨x, rfl⟩ := x.mk_surjective
    exact congrArg CohomologyClass.mk (Cocycle.ext (Cochain.comp_smul _ _ _ (zero_add n)))

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable (R : Type) [CommRing R] in
theorem _root_.GlobalTheory.EtC.Tr.along_id (X : Scheme.{0}) (F : _root_.GlobalTheory.EtC.Shv R) (n : ℤ)
    (x : _root_.GlobalTheory.EtC.H R (_root_.GlobalTheory.EtC.sch.obj X) F n) :
    _root_.GlobalTheory.EtC.Tr.along R F n (𝟙 _) x = x := by
  have hid : (𝟙 (_root_.GlobalTheory.EtC.Tr.freeSch R X)) =
      (_root_.GlobalTheory.EtC.free R).map (yoneda.map (𝟙 X)) := by
    simp
  rw [hid]
  unfold _root_.GlobalTheory.EtC.Tr.along
  rw [_root_.GlobalTheory.EtC.Tr.chainMap_free, CategoryTheory.Functor.map_id]
  exact _root_.GlobalTheory.EtC.pull_id R _ F n x

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable (R : Type) [CommRing R] in

theorem _root_.GlobalTheory.EtC.Tr.along_free {X Z : Scheme.{0}} (g : X ⟶ Z)
    (F : _root_.GlobalTheory.EtC.Shv R) (n : ℤ) :
    _root_.GlobalTheory.EtC.Tr.along R F n ((_root_.GlobalTheory.EtC.free R).map (yoneda.map g)) =
      _root_.GlobalTheory.EtC.pull R (_root_.GlobalTheory.EtC.sch.map g) F n := by
  unfold _root_.GlobalTheory.EtC.Tr.along _root_.GlobalTheory.EtC.pull
  rw [_root_.GlobalTheory.EtC.Tr.chainMap_free]

def trH {Z X : Scheme.{0}} (f : Z ⟶ X) (F : Shv R) (n : ℤ) : H R (sch.obj Z) F n →+ H R (sch.obj X) F n :=
  along R F n (transfer R f)

def trL {Z X : Scheme.{0}} (f : Z ⟶ X) (F : Shv R) (n : ℤ) : H R (sch.obj Z) F n →ₗ[R] H R (sch.obj X) F n :=
  alongL R F n (transfer R f)

theorem trH_id (X : Scheme.{0}) (F : Shv R) (n : ℤ) (x : H R (sch.obj X) F n) : trH R (𝟙 X) F n x = x := by
  rw [trH, transfer_id]; exact along_id R X F n x

end Trace

section Twist

def trHt (q : ℕ) {Z X : Scheme.{0}} (f : Z ⟶ X) (n i : ℤ) : Ht q (sch.obj Z) n i →+ Ht q (sch.obj X) n i :=
  trH (ZMod q) f (tw q i) n

theorem trHt_id (q : ℕ) (X : Scheme.{0}) (n i : ℤ) (x : Ht q (sch.obj X) n i) : trHt q (𝟙 X) n i x = x :=
  trH_id (ZMod q) X (tw q i) n x

end Twist

section Adic

variable (l : ℕ) [Fact l.Prime]

def RedCompat {Z X : Scheme.{0}} (f : Z ⟶ X) (n i : ℤ) : Prop :=
  ∀ (k : ℕ) (x : Ht (l ^ (k + 1)) (sch.obj Z) n i),
    red (l ^ (k + 1)) (l ^ k) (sch.obj X) n i (trHt (l ^ (k + 1)) f n i x) = trHt (l ^ k) f n i (red (l ^ (k + 1)) (l ^ k) (sch.obj Z) n i x)

def IsTrHl {Z X : Scheme.{0}} (f : Z ⟶ X) (n i : ℤ) (φ : Hl l (sch.obj Z) n i →ₗ[ℤ_[l]] Hl l (sch.obj X) n i) : Prop :=
  ∀ (x : Hl l (sch.obj Z) n i) (k : ℕ), (φ x).1 k = trHt (l ^ k) f n i (x.1 k)

def trHl {Z X : Scheme.{0}} (f : Z ⟶ X) (n i : ℤ) : Hl l (sch.obj Z) n i →ₗ[ℤ_[l]] Hl l (sch.obj X) n i :=
  pick (IsTrHl l f n i)

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
variable (l : ℕ) [Fact l.Prime] in

theorem _root_.GlobalTheory.EtC.Tr.trHl_spec {Z X : Scheme.{0}} {f : Z ⟶ X} {n i : ℤ}
    (h : _root_.GlobalTheory.EtC.Tr.RedCompat l f n i) :
    _root_.GlobalTheory.EtC.Tr.IsTrHl l f n i (_root_.GlobalTheory.EtC.Tr.trHl l f n i) := by
  apply _root_.GlobalTheory.EtC.pick_spec
  refine ⟨{ toFun := fun x => ⟨fun k => _root_.GlobalTheory.EtC.Tr.trHt (l ^ k) f n i (x.1 k), ?_⟩
            map_add' := ?_
            map_smul' := ?_ }, fun x k => rfl⟩
  · intro k
    show _root_.GlobalTheory.EtC.red (l ^ (k + 1)) (l ^ k) (_root_.GlobalTheory.EtC.sch.obj X) n i
        (_root_.GlobalTheory.EtC.Tr.trHt (l ^ (k + 1)) f n i (x.1 (k + 1))) =
      _root_.GlobalTheory.EtC.Tr.trHt (l ^ k) f n i (x.1 k)
    rw [h k (x.1 (k + 1))]
    congr 1
    exact x.2 k
  · intro x y
    apply Subtype.ext
    funext k
    exact map_add (_root_.GlobalTheory.EtC.Tr.trHt (l ^ k) f n i) (x.1 k) (y.1 k)
  · intro r x
    apply Subtype.ext
    funext k
    have h1 := _root_.GlobalTheory.EtC.HtL.smul_eq l k k le_rfl
      (_root_.GlobalTheory.EtC.sch.obj Z) n i r (x.1 k)
    have h2 := _root_.GlobalTheory.EtC.HtL.smul_eq l k k le_rfl
      (_root_.GlobalTheory.EtC.sch.obj X) n i r (_root_.GlobalTheory.EtC.Tr.trHt (l ^ k) f n i (x.1 k))
    exact (congrArg (_root_.GlobalTheory.EtC.Tr.trHt (l ^ k) f n i) h1).trans
      ((map_nsmul _ _ _).trans h2.symm)

def trHQ {Z X : Scheme.{0}} (f : Z ⟶ X) (n i : ℤ) : HQ l (sch.obj Z) n i →ₗ[ℚ_[l]] HQ l (sch.obj X) n i :=
  (trHl l f n i).baseChange ℚ_[l]

end Adic

example (X : Scheme.{0}) (n : ℤ) (x : Ht 5 (sch.obj X) n 2) : trHt 5 (𝟙 X) n 2 x = x := trHt_id 5 X n 2 x

example : transfer ℤ (𝟙 (Spec (CommRingCat.of (Polynomial ℤ)))) = 𝟙 _ := transfer_id ℤ _

end GlobalTheory.EtC.Tr
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SmoothCartan
section
noncomputable section

open GlobalTheory.BorelCoh GroundTheory.Automorphic

namespace GlobalTheory.Mt

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

structure CartanData (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) where

  lie : IsExpLieAlgebra G 𝔤

  closed : IsClosed (G : Set 𝔸ˣ)

  K : Subgroup G
  compact : IsCompact (K : Set G)

  k : Submodule ℝ 𝔤

  p : Submodule ℝ 𝔤
  isCompl : IsCompl k p
  bracket_kk : ∀ X ∈ k, ∀ Y ∈ k, lie.bracket X Y ∈ k
  bracket_kp : ∀ X ∈ k, ∀ Y ∈ p, lie.bracket X Y ∈ p
  bracket_pp : ∀ X ∈ p, ∀ Y ∈ p, lie.bracket X Y ∈ k
  Ad_p : ∀ κ ∈ K, ∀ Y ∈ p, lie.Ad κ Y ∈ p
  expG_k : ∀ X ∈ k, lie.expG X ∈ K

  cartan : ∀ g : G, ∃! x : p × K, g = lie.expG (x.1 : 𝔤) * (x.2 : G)

  smooth_cartan : ∀ ℓ : 𝔤 →L[ℝ] ℂ, lie.IsSmoothFun (F := ℂ) fun g => ℓ ((cartan g).exists.choose.1 : 𝔤)

  B : LinearMap.BilinForm ℝ 𝔤
  B_symm : ∀ X Y, B X Y = B Y X
  B_Ad : ∀ g X Y, B (lie.Ad g X) (lie.Ad g Y) = B X Y
  B_p : ∀ X ∈ p, X ≠ 0 → 0 < B X X
  B_k : ∀ X ∈ k, X ≠ 0 → B X X < 0
  B_kp : ∀ X ∈ k, ∀ Y ∈ p, B X Y = 0

namespace CartanData

variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (D : CartanData G 𝔤)

def adP (κ : D.K) (Y : D.p) : D.p := ⟨D.lie.Ad (κ : G) Y, D.Ad_p κ κ.2 Y Y.2⟩

section Rel

variable {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]

def cocyc (L : D.p →ₗ[ℝ] Module.End ℂ M) (κ : D.K → Module.End ℂ M) (q : ℕ) :
    Submodule ℂ (D.p [⋀^Fin q]→ₗ[ℝ] M) :=
  Submodule.span ℂ {f | f ∈ relCo D.adP κ ⊤ q ∧ gd L f = 0}

def cobd (L : D.p →ₗ[ℝ] Module.End ℂ M) (κ : D.K → Module.End ℂ M) : (q : ℕ) → Submodule ℂ (D.p [⋀^Fin q]→ₗ[ℝ] M)
  | 0 => ⊥
  | q + 1 => Submodule.span ℂ (gd L '' relCo D.adP κ ⊤ q)

abbrev Hrel (L : D.p →ₗ[ℝ] Module.End ℂ M) (κ : D.K → Module.End ℂ M) (q : ℕ) : Type _ :=
  D.cocyc L κ q ⧸ (D.cobd L κ q).comap (D.cocyc L κ q).subtype

end Rel

section Unitary

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def toBanach (π : UnitaryRep G H) : BanachRep G H :=
  ⟨(unitary (H →L[ℂ] H)).subtype.comp π.toHom, fun v => π.continuous_orbit' v⟩

abbrev SmV (π : UnitaryRep G H) : Submodule ℂ H := D.lie.smoothVectors (toBanach π)

def dOp (π : UnitaryRep G H) (X : 𝔤) : Module.End ℂ (D.SmV π) where
  toFun v := ⟨D.lie.derivOp (toBanach π) X v, D.lie.isSmoothVector_derivOp (toBanach π) v.2 X⟩
  map_add' v w := Subtype.ext (D.lie.derivOp_add (toBanach π) v.2 w.2 X)
  map_smul' c v := Subtype.ext (D.lie.derivOp_smul (toBanach π) v.2 c X)

def gOp (π : UnitaryRep G H) (g : G) : Module.End ℂ (D.SmV π) :=
  ((toBanach π).toHom g : H →L[ℂ] H).toLinearMap.restrict fun v hv => D.lie.isSmoothVector_map (toBanach π) hv g

variable {d : ℕ}

def dξ (ξ : G →* Matrix (Fin d) (Fin d) ℂ) (X : 𝔤) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => D.lie.rightDeriv (F := ℂ) X (fun g => ξ g i j) 1

def tOp (π : UnitaryRep G H) (ξ : G →* Matrix (Fin d) (Fin d) ℂ) (X : 𝔤) : Module.End ℂ (Fin d → D.SmV π) :=
  LinearMap.pi fun i => (D.dOp π X).comp (LinearMap.proj i) + ∑ j, D.dξ ξ X i j • LinearMap.proj j

def gkL (π : UnitaryRep G H) (ξ : G →* Matrix (Fin d) (Fin d) ℂ) : D.p →ₗ[ℝ] Module.End ℂ (Fin d → D.SmV π) :=
  (Module.finBasis ℝ D.p).constr ℝ fun i => D.tOp π ξ ((Module.finBasis ℝ D.p) i : 𝔤)

def gkK (π : UnitaryRep G H) (ξ : G →* Matrix (Fin d) (Fin d) ℂ) (κ : D.K) : Module.End ℂ (Fin d → D.SmV π) :=
  LinearMap.pi fun i => ∑ j, ξ (κ : G) i j • (D.gOp π κ).comp (LinearMap.proj j)

abbrev HGK (π : UnitaryRep G H) (ξ : G →* Matrix (Fin d) (Fin d) ℂ) (q : ℕ) : Type _ :=
  D.Hrel (D.gkL π ξ) (D.gkK π ξ) q

end Unitary

end CartanData

end GlobalTheory.Mt
end
end

