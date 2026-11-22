import Development.EtaleCohomology.EtaleSheaves.H1MultiplicativeGroup
import Development.EtaleCohomology.EtaleSheaves.Bundle0025
import Development.EtaleCohomology.EtaleSheaves.Bundle0024
import Development.EtaleCohomology.EtaleSheaves.Bundle0026

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafDescCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H1MultiplicativeGroup
open scoped TensorProduct

namespace LateralTheory.E.LeafDescCut

def d0 (A : Type) [CommRing A] (U : Cov A) : U.B →ₐ[A] U.B ⊗[A] U.B := Algebra.TensorProduct.includeRight

def d1 (A : Type) [CommRing A] (U : Cov A) : U.B →ₐ[A] U.B ⊗[A] U.B := Algebra.TensorProduct.includeLeft

def p12 (A : Type) [CommRing A] (U : Cov A) : U.B ⊗[A] U.B →ₐ[A] U.B ⊗[A] (U.B ⊗[A] U.B) :=
  Algebra.TensorProduct.map (AlgHom.id A U.B) Algebra.TensorProduct.includeLeft

def p13 (A : Type) [CommRing A] (U : Cov A) : U.B ⊗[A] U.B →ₐ[A] U.B ⊗[A] (U.B ⊗[A] U.B) :=
  Algebra.TensorProduct.map (AlgHom.id A U.B) Algebra.TensorProduct.includeRight

def p23 (A : Type) [CommRing A] (U : Cov A) : U.B ⊗[A] U.B →ₐ[A] U.B ⊗[A] (U.B ⊗[A] U.B) :=
  Algebra.TensorProduct.includeRight

def cob1 (A : Type) [CommRing A] (U : Cov A) : (U.B ⊗[A] U.B)ˣ →* (U.B ⊗[A] (U.B ⊗[A] U.B))ˣ :=
  Units.map (p13 A U : U.B ⊗[A] U.B →* U.B ⊗[A] (U.B ⊗[A] U.B)) /
    (Units.map (p12 A U : U.B ⊗[A] U.B →* U.B ⊗[A] (U.B ⊗[A] U.B)) *
      Units.map (p23 A U : U.B ⊗[A] U.B →* U.B ⊗[A] (U.B ⊗[A] U.B)))

def cob0 (A : Type) [CommRing A] (U : Cov A) : U.Bˣ →* (U.B ⊗[A] U.B)ˣ :=
  Units.map (d0 A U : U.B →* U.B ⊗[A] U.B) / Units.map (d1 A U : U.B →* U.B ⊗[A] U.B)

def Z1 (A : Type) [CommRing A] (U : Cov A) : Subgroup (U.B ⊗[A] U.B)ˣ := (cob1 A U).ker

def B1 (A : Type) [CommRing A] (U : Cov A) : Subgroup (U.B ⊗[A] U.B)ˣ := (cob0 A U).range

abbrev Cech (A : Type) [CommRing A] (U : Cov A) : Type := Additive (Z1 A U ⧸ (B1 A U).subgroupOf (Z1 A U))

def cls (A : Type) [CommRing A] (U : Cov A) (u : Z1 A U) : Cech A U := Additive.ofMul (QuotientGroup.mk u)

def tmap (A : Type) [CommRing A] (U V : Cov A) (g : U.B →ₐ[A] V.B) : (U.B ⊗[A] U.B)ˣ →* (V.B ⊗[A] V.B)ˣ :=
  Units.map (Algebra.TensorProduct.map g g : U.B ⊗[A] U.B →* V.B ⊗[A] V.B)

def LeafZMap : Prop := ∀ (A : Type) [CommRing A] (U V : Cov A) (g : U.B →ₐ[A] V.B) (u : (U.B ⊗[A] U.B)ˣ),
  u ∈ Z1 A U → tmap A U V g u ∈ Z1 A V

theorem mem_Z1_iff_cocycle (A : Type) [CommRing A] (U : Cov A) (u : (U.B ⊗[A] U.B)ˣ) :
    u ∈ Z1 A U ↔ p13 A U (u : U.B ⊗[A] U.B) = p12 A U u * p23 A U u := by
  rw [Z1, MonoidHom.mem_ker, cob1, MonoidHom.div_apply, div_eq_one, MonoidHom.mul_apply, Units.ext_iff]
  simp

abbrev g3 (A : Type) [CommRing A] (U V : Cov A) (g : U.B →ₐ[A] V.B) :
    U.B ⊗[A] (U.B ⊗[A] U.B) →ₐ[A] V.B ⊗[A] (V.B ⊗[A] V.B) :=
  Algebra.TensorProduct.map g (Algebra.TensorProduct.map g g)

theorem p12_tensorProduct_map_eq_g3_p12 (A : Type) [CommRing A] (U V : Cov A) (g : U.B →ₐ[A] V.B) (x : U.B ⊗[A] U.B) :
    p12 A V (Algebra.TensorProduct.map g g x) = g3 A U V g (p12 A U x) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [p12]

theorem p13_tensorProduct_map_eq_g3_p13 (A : Type) [CommRing A] (U V : Cov A) (g : U.B →ₐ[A] V.B) (x : U.B ⊗[A] U.B) :
    p13 A V (Algebra.TensorProduct.map g g x) = g3 A U V g (p13 A U x) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [p13]

theorem p23_tensorProduct_map_eq_g3_p23 (A : Type) [CommRing A] (U V : Cov A) (g : U.B →ₐ[A] V.B) (x : U.B ⊗[A] U.B) :
    p23 A V (Algebra.TensorProduct.map g g x) = g3 A U V g (p23 A U x) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  apply Algebra.TensorProduct.ext'
  intro a b
  simp [p23]

theorem zmap : LeafZMap := by
  intro A _ U V g u hu
  rw [mem_Z1_iff_cocycle] at hu ⊢
  have ht : ((tmap A U V g u : (V.B ⊗[A] V.B)ˣ) : V.B ⊗[A] V.B) = Algebra.TensorProduct.map g g (u : U.B ⊗[A] U.B) := rfl
  rw [ht, p12_tensorProduct_map_eq_g3_p12, p13_tensorProduct_map_eq_g3_p13, p23_tensorProduct_map_eq_g3_p23, hu, map_mul]

def LeafDescH : Prop := Hyps → ∀ (A : Type) [CommRing A], ∃ c : ∀ U : Cov A, Cech A U ≃+ kerH A U,
  ∀ (U V : Cov A) (g : U.B →ₐ[A] V.B) (u : Z1 A U) (v : Z1 A V), (v : (V.B ⊗[A] V.B)ˣ) = tmap A U V g u →
    (c V (cls A V v) : H ℤ (sp A) Gm 1) = c U (cls A U u)

def LeafDescP : Prop := ∀ (A : Type) [CommRing A], ∃ c : ∀ U : Cov A, Cech A U ≃+ kerP A U,
  ∀ (U V : Cov A) (g : U.B →ₐ[A] V.B) (u : Z1 A U) (v : Z1 A V), (v : (V.B ⊗[A] V.B)ˣ) = tmap A U V g u →
    (c V (cls A V v) : Additive (CommRing.Pic A)) = c U (cls A U u)

theorem goal_of (hH : LeafDescH) (hP : LeafDescP) : LateralTheory.E.H1MultiplicativeGroup.LeafDesc := by
  intro hy A _
  obtain ⟨cH, hcH⟩ := hH hy A
  obtain ⟨cP, hcP⟩ := hP A
  refine ⟨fun U => (cH U).symm.trans (cP U), ?_⟩
  intro U V g x hU hV
  obtain ⟨u, hu⟩ : ∃ u : Z1 A U, cls A U u = (cH U).symm ⟨x, hU⟩ := by
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul ((cH U).symm ⟨x, hU⟩))
    exact ⟨u, by rw [cls, hu]; rfl⟩
  let v : Z1 A V := ⟨tmap A U V g u, zmap A U V g u u.2⟩
  have h1 := hcH U V g u v rfl
  have h2 := hcP U V g u v rfl
  have hv : (cH V).symm ⟨x, hV⟩ = cls A V v := by
    apply (cH V).injective
    rw [AddEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [h1, hu, AddEquiv.apply_symm_apply]
  simp only [AddEquiv.trans_apply]
  rw [← hu, hv, h2]

end LateralTheory.E.LeafDescCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafFreeLocPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut LateralTheory.E.LeafSqPf

namespace LateralTheory.E.LeafFreeLocPf

lemma etLoc_top {T : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ T) → Prop} (h : ∀ V k, P V k) : EtLoc T P :=
  ⟨⊤, GrothendieckTopology.top_mem _ _, fun V k _ => h V k⟩

lemma etLoc_and {T : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ T) → Prop} (hP : EtLoc T P) (hQ : EtLoc T Q) :
    EtLoc T (fun V k => P V k ∧ Q V k) := by
  obtain ⟨S, hS, hS'⟩ := hP
  obtain ⟨S', hT, hT'⟩ := hQ
  exact ⟨S ⊓ S', GrothendieckTopology.intersection_covering _ hS hT, fun V k hk => ⟨hS' V k hk.1, hT' V k hk.2⟩⟩

lemma etLoc_mono {T : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ T) → Prop} (hP : EtLoc T P)
    (h : ∀ V k, P V k → Q V k) : EtLoc T Q := by
  obtain ⟨S, hS, hS'⟩ := hP
  exact ⟨S, hS, fun V k hk => h V k (hS' V k hk)⟩

lemma alg {S X Y Z : Type*} [CommRing S] (g : X → Z) (f : Y → Z) (D : Submodule S (X →₀ S))
    (h1 : ∀ a, (∃ u, f u = g a) → Finsupp.single a 1 ∈ D)
    (h2 : ∀ a b, g a = g b → Finsupp.single a 1 - Finsupp.single b 1 ∈ D)
    (x : X →₀ S) (y : Y →₀ S) (h : Finsupp.mapDomain g x = Finsupp.mapDomain f y) : x ∈ D := by
  classical
  let v : Z → (X →₀ S) ⧸ D := fun z =>
    if hz : (∃ a, g a = z) ∧ ¬ ∃ u, f u = z then D.mkQ (Finsupp.single hz.1.choose 1) else 0
  let θ := Finsupp.linearCombination S v
  have hv : ∀ a, v (g a) = D.mkQ (Finsupp.single a 1) := by
    intro a
    simp only [v]
    split_ifs with hz
    · have hc := hz.1.choose_spec
      rw [eq_comm, ← sub_eq_zero, ← LinearMap.map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact h2 _ _ hc.symm
    · have : ∃ u, f u = g a := by
        by_contra hn
        exact hz ⟨⟨a, rfl⟩, hn⟩
      rw [eq_comm, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact h1 a this
  have hx : ∀ x' : X →₀ S, θ (Finsupp.mapDomain g x') = D.mkQ x' := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq => rw [Finsupp.mapDomain_add, map_add, hp, hq, map_add]
    | single a r =>
      rw [Finsupp.mapDomain_single]
      simp only [θ, Finsupp.linearCombination_single, hv]
      rw [← LinearMap.map_smul, Finsupp.smul_single_one]
  have hy : ∀ y' : Y →₀ S, θ (Finsupp.mapDomain f y') = 0 := by
    intro y
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq => rw [Finsupp.mapDomain_add, map_add, hp, hq, add_zero]
    | single u r =>
      rw [Finsupp.mapDomain_single]
      simp only [θ, Finsupp.linearCombination_single, v]
      rw [dif_neg (fun hz => hz.2 ⟨u, rfl⟩), smul_zero]
  have : D.mkQ x = 0 := by rw [← hx, h, hy]
  simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using this

lemma mapApp (R : Type) [CommRing R] {X Y : PSh} (φ : X ⟶ Y) (V : Scheme.{0}) (z : ((freeP R).obj X).obj (op V)) :
    (((freeP R).map φ).app (op V)).hom z =
      Finsupp.mapDomain (fun x : ULift (X.obj (op V)) => ULift.up (φ.app (op V) x.down)) z := rfl

lemma natP (R : Type) [CommRing R] {X Y : PSh} (φ : X ⟶ Y) {V T : Scheme.{0}} (k : V ⟶ T)
    (z : ((freeP R).obj X).obj (op T)) :
    (((freeP R).map φ).app (op V)).hom ((((freeP R).obj X).map k.op).hom z) =
      (((freeP R).obj Y).map k.op).hom ((((freeP R).map φ).app (op T)).hom z) :=
  congrArg (fun m => m.hom z) (((freeP R).map φ).naturality k.op)

theorem LeafFreeLoc_of (_hRel : LeafRel) : LeafFreeLoc := by
  intro R _ P U E' E fst snd f _ g hpb h1 h2
  have hinj : ∀ V : Scheme.{0}, Function.Injective (f.app (op V)) := fun V =>
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app f).1 inferInstance (op V))
  have hex : ∀ (V : Scheme.{0}) (u : U.obj (op V)) (a : E'.obj (op V)), f.app (op V) u = g.app (op V) a →
      ∃ p, fst.app (op V) p = u ∧ snd.app (op V) p = a :=
    fun V u a h => Types.exists_of_isPullback (hpb.map ((evaluation _ _).obj (op V))) u a h
  refine ⟨?_, ?_⟩
  · show ∀ (T : Scheme.{0}) (z : ULift (E.obj (op T)) →₀ ULift R), EtLoc T fun V k =>
      ∃ (x : ULift (E'.obj (op V)) →₀ ULift R) (y : ULift (U.obj (op V)) →₀ ULift R),
        Finsupp.mapDomain (fun x : ULift (E'.obj (op V)) => ULift.up (g.app (op V) x.down)) x +
          Finsupp.mapDomain (fun x : ULift (U.obj (op V)) => ULift.up (f.app (op V) x.down)) y =
        Finsupp.mapDomain (fun x : ULift (E.obj (op T)) => ULift.up (E.map k.op x.down)) z
    intro T z
    induction z using Finsupp.induction_linear with
    | zero => exact etLoc_top fun V k => ⟨0, 0, by simp⟩
    | add p q hp hq =>
      exact etLoc_mono (etLoc_and hp hq) fun V k ⟨⟨x1, y1, e1⟩, ⟨x2, y2, e2⟩⟩ =>
        ⟨x1 + x2, y1 + y2, by
          rw [Finsupp.mapDomain_add, Finsupp.mapDomain_add, Finsupp.mapDomain_add, ← e1, ← e2]; abel⟩
    | single a r =>
      refine etLoc_mono (h1 T a.down) fun V k hk => ?_
      rcases hk with ⟨u, hu⟩ | ⟨b, hb⟩
      · refine ⟨0, Finsupp.single (ULift.up u) r, ?_⟩
        rw [Finsupp.mapDomain_zero, zero_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single, hu]
      · refine ⟨Finsupp.single (ULift.up b) r, 0, ?_⟩
        rw [Finsupp.mapDomain_zero, add_zero, Finsupp.mapDomain_single, Finsupp.mapDomain_single, hb]
  · intro T x y hxy
    let D : Submodule (ULift R) (ULift (E'.obj (op T)) →₀ ULift R) :=
      { carrier := {x | EtLoc T fun V k => ∃ w : ULift (P.obj (op V)) →₀ ULift R,
          Finsupp.mapDomain (fun x : ULift (P.obj (op V)) => ULift.up (snd.app (op V) x.down)) w =
            Finsupp.mapDomain (fun x : ULift (E'.obj (op T)) => ULift.up (E'.map k.op x.down)) x}
        zero_mem' := etLoc_top fun V k => ⟨0, by rw [Finsupp.mapDomain_zero, Finsupp.mapDomain_zero]⟩
        add_mem' := fun {a b} ha hb => etLoc_mono (etLoc_and ha hb) fun V k ⟨⟨w1, e1⟩, ⟨w2, e2⟩⟩ =>
          ⟨w1 + w2, by rw [Finsupp.mapDomain_add, Finsupp.mapDomain_add, e1, e2]⟩
        smul_mem' := fun c a ha => etLoc_mono ha fun V k ⟨w, e⟩ =>
          ⟨c • w, by rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_smul, e]⟩ }
    have hxD : x ∈ D := by
      refine alg (fun a : ULift (E'.obj (op T)) => ULift.up (g.app (op T) a.down))
        (fun u : ULift (U.obj (op T)) => ULift.up (f.app (op T) u.down)) D ?_ ?_ x (-y) ?_
      · rintro a ⟨u, hu⟩
        obtain ⟨p, -, hp2⟩ := hex T u.down a.down (congrArg ULift.down hu)
        refine etLoc_top fun V k => ⟨Finsupp.single (ULift.up (P.map k.op p)) 1, ?_⟩
        rw [Finsupp.mapDomain_single, Finsupp.mapDomain_single, ← hp2, NatTrans.naturality_apply]
      · intro a b hab
        have hab' : g.app (op T) a.down = g.app (op T) b.down := congrArg ULift.down hab
        show EtLoc T fun V k => ∃ w : ULift (P.obj (op V)) →₀ ULift R,
          Finsupp.mapDomain (fun x : ULift (P.obj (op V)) => ULift.up (snd.app (op V) x.down)) w =
            Finsupp.mapDomain (fun x : ULift (E'.obj (op T)) => ULift.up (E'.map k.op x.down))
              (Finsupp.single a 1 - Finsupp.single b 1)
        refine etLoc_mono (h2 T a.down b.down hab') fun V k hk => ?_
        rcases hk with he | ⟨u, hu⟩
        · refine ⟨0, ?_⟩
          rw [Finsupp.mapDomain_zero, Finsupp.mapDomain_sub, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
          simp only [he, sub_self]
        · have ga : f.app (op V) u = g.app (op V) (E'.map k.op a.down) := by
            rw [hu, NatTrans.naturality_apply]
          have gb : f.app (op V) u = g.app (op V) (E'.map k.op b.down) := by
            rw [hu, hab', NatTrans.naturality_apply]
          obtain ⟨pa, -, hpa⟩ := hex V u _ ga
          obtain ⟨pb, -, hpb'⟩ := hex V u _ gb
          refine ⟨Finsupp.single (ULift.up pa) 1 - Finsupp.single (ULift.up pb) 1, ?_⟩
          rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_sub]
          simp only [Finsupp.mapDomain_single, hpa, hpb']
      · change (((freeP R).map g).app (op T)).hom x = (((freeP R).map f).app (op T)).hom (-y)
        rw [map_neg]
        exact eq_neg_of_add_eq_zero_left hxy
    refine etLoc_mono hxD fun V k hV => ?_
    obtain ⟨w0, hw0⟩ := hV
    obtain ⟨w, hw'⟩ : ∃ w : ((freeP R).obj P).obj (op V),
        (((freeP R).map snd).app (op V)).hom w = (((freeP R).obj E').map k.op).hom x :=
      ⟨w0, hw0⟩
    refine ⟨w, hw', ?_⟩
    have hfi : Function.Injective (fun v : ULift (U.obj (op V)) => ULift.up (f.app (op V) v.down)) :=
      fun a b h => ULift.ext _ _ (hinj V (congrArg ULift.down h))
    have fInj : Function.Injective (((freeP R).map f).app (op V)).hom := by
      intro a b h
      rw [mapApp, mapApp] at h
      exact Finsupp.mapDomain_injective hfi h
    have commP : ∀ w : ((freeP R).obj P).obj (op V),
        (((freeP R).map f).app (op V)).hom ((((freeP R).map fst).app (op V)).hom w) =
          (((freeP R).map g).app (op V)).hom ((((freeP R).map snd).app (op V)).hom w) := by
      intro w
      have := congrArg (fun φ => ((freeP R).map φ).app (op V)) hpb.w
      simp only [Functor.map_comp, NatTrans.comp_app] at this
      exact congrArg (fun m => m.hom w) this
    have hg : (((freeP R).map g).app (op T)).hom x = -(((freeP R).map f).app (op T)).hom y :=
      eq_neg_of_add_eq_zero_left hxy
    apply fInj
    rw [commP, hw', natP, hg, map_neg, map_neg, natP]

end LateralTheory.E.LeafFreeLocPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafKumSpecPfEv
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafKumSpecPf

theorem freeGen_res (R : Type) [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen Sec.res
  have := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
    (ModuleCat.freeMk (ULift.up x))
  have hm : (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up ((P.map g.op) x)) := by
    simp [freeP, ModuleCat.freeMk]
    first | (rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl) | (erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl) | (simp [Finsupp.mapDomain_single]; rfl)
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hm] at this
  exact this.symm

end LateralTheory.E.LeafKumSpecPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafLocPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafLocPf

def overIso {R : Type} [CommRing R] (X : Scheme.{0}) (F G : Shv R)
    (e : ∀ U : Scheme.{0}, (U ⟶ X) → (Sec F U ≃ₗ[ULift.{1} R] Sec G U))
    (he : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), e V (g ≫ x) (Sec.res g s) = Sec.res g (e U x s)) :
    F.over X ≅ G.over X :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun Y => (e Y.unop.left Y.unop.hom).toModuleIso) (by
    intro Y Y' f
    ext s
    have h := he f.unop.left Y.unop.hom s
    rw [Over.w f.unop] at h
    exact h))

def LocOver : Prop := Hyps → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F G : Shv R),
  Nonempty (F.over X ≅ G.over X) → ∀ n : ℤ, Nonempty (H R (sch.obj X) F n ≃+ H R (sch.obj X) G n)

theorem LeafLoc_of (hO : LocOver) : LateralTheory.E.LeafTwistPf.LeafLoc := by
  intro hy R _ X F G e he n
  exact hO hy R X F G ⟨overIso X F G e he⟩ n

abbrev secCx {R : Type} [CommRing R] (F : Shv R) (X : Scheme.{0}) : CochainComplex (ModuleCat.{1} (ULift.{1} R)) ℤ :=
  ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op X)).mapHomologicalComplex _).obj (res R F)

def LocSec : Prop := Hyps → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F : Shv R) (n : ℤ),
  Nonempty (H R (sch.obj X) F n ≃+ (secCx F X).homology n)

def LocSlice : Prop := Hyps → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F G : Shv R),
  Nonempty (F.over X ≅ G.over X) → ∀ n : ℤ, Nonempty ((secCx F X).homology n ≃+ (secCx G X).homology n)

theorem LocOver_of (hS : LocSec) (hL : LocSlice) : LocOver := by
  intro hy R _ X F G hi n
  obtain ⟨a⟩ := hS hy R X F n
  obtain ⟨b⟩ := hS hy R X G n
  obtain ⟨c⟩ := hL hy R X F G hi n
  exact ⟨(a.trans c).trans b.symm⟩

theorem LeafLoc_of' (hS : LocSec) (hL : LocSlice) : LateralTheory.E.LeafTwistPf.LeafLoc :=
  LeafLoc_of (LocOver_of hS hL)

end LateralTheory.E.LeafLocPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafOfRingsLocInjPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8.TwSec

theorem jointlySurj_prec (P : MorphismProperty Scheme.{0}) : Scheme.JointlySurjective (Scheme.precoverage P) :=
  inferInstance

theorem LeafOfRingsLocInj_of : LeafOfRingsLocInj := by
  intro R _ M U t ht u
  have h0 : (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U) t =
      (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).app (op U) 0 := by
    have : ofRings.sec M U t = 0 := ht
    simp only [ofRings.sec] at this
    rw [map_zero]
    exact this
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) t 0 h0
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  have := jointlySurj_prec @Etale
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq u
  refine ⟨𝒰.X i, 𝒰.f i, 𝒰.map_prop i, ⟨y, hy⟩, ?_⟩
  have hm := hle _ _ (Presieve.ofArrows.mk i)
  have hm' : ((Scheme.Γ ⋙ M).map (𝒰.f i).op).hom t = ((Scheme.Γ ⋙ M).map (𝒰.f i).op).hom 0 := hm
  rw [map_zero] at hm'
  exact hm'

end LateralTheory.E.E8.TwSec
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafOfRingsLocSurjPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafOfRingsLocSurjPf

theorem cover_hit {X : Scheme.{0}} (S : Sieve X) (hS : S ∈ Scheme.etaleTopology X) (x : X) :
    ∃ (U : Scheme.{0}) (w : U ⟶ X), Etale w ∧ x ∈ Set.range w ∧ S.arrows w := by
  obtain ⟨𝒰, h𝒰⟩ := (Scheme.mem_grothendieckTopology_iff).1 hS
  obtain ⟨i, hi⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 x
  exact ⟨𝒰.X i, 𝒰.f i, 𝒰.map_prop i, hi, h𝒰 _ _ (Presieve.ofArrows.mk i)⟩

theorem LeafOfRingsLocSurj_of : LateralTheory.E.E8.TwSec.LeafOfRingsLocSurj := by
  intro R _ M X s x
  have hS := Presheaf.imageSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (U := op X) s
  obtain ⟨U, w, hw, hx, t, ht⟩ := cover_hit _ hS x
  exact ⟨U, w, hw, hx, t, ht.symm⟩

end LateralTheory.E.LeafOfRingsLocSurjPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafOneLocPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafOneLocPf

theorem freeGen_res (R : Type) [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen Sec.res
  have h := congrArg (fun f => f.hom (ModuleCat.freeMk (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at h
  have h2 : (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} (P.map g.op x)) :=
    ModuleCat.free_map_apply (R := ULift.{1} R) _ _
  exact h.symm.trans (congrArg _ h2)

theorem ev_res {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (Sx.res g x) := by
  unfold ev
  have hn := congrArg (fun f => f.hom (freeGen R _ U x))
    ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hn
  change _ = _ at hn
  rw [Sx.res, ← freeGen_res]
  exact hn.symm

def LeafPrimLoc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) →
  Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))

theorem LeafOneLoc_of (hprim : LeafPrimLoc) : LateralTheory.E.LeafRingUnitPf.LeafOneLoc := by
  intro q _ E hE α hα U x
  obtain ⟨S, hS, hP⟩ := hprim q U (hE U ⟨x⟩)
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨ζ⟩ := hP V g hg
  exact ⟨ζ, (ev_res α.1 0 0 (by simp) g x).trans (hα V (Sx.res g x) ζ)⟩

end LateralTheory.E.LeafOneLocPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwPtPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8.TwSec

theorem twF_res_comp {q : ℕ} (j : ℤ) {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (x : (twF q j).obj Γ(Z, ⊤)) :
    ((twF q j).map (Scheme.Γ.map (a ≫ b).op)).hom x =
      ((twF q j).map (Scheme.Γ.map a.op)).hom (((twF q j).map (Scheme.Γ.map b.op)).hom x) := by
  rw [op_comp, Functor.map_comp, Functor.map_comp]; rfl

theorem twF_map_cls {q : ℕ} (j : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (ζ : Prim q A) (c : ZMod q) :
    ((twF q j).map f).hom (ULift.up c • twCls j ζ) = ULift.up c • twCls j (ζ.map f.hom) := by
  rw [map_smul]
  congr 1
  unfold twCls
  change Submodule.mapQ _ _ _ (twRel_le q j f.hom) _ = _
  rw [Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem twF_eq_zero_of_not_unit {q : ℕ} (j : ℤ) {A : CommRingCat.{0}} (hq : ¬ IsUnit (q : A)) (t : (twF q j).obj A) :
    t = 0 := by
  haveI : IsEmpty (Prim q A) := ⟨fun ζ => hq ζ.2.1⟩
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  rw [Subsingleton.elim f 0]
  exact Submodule.Quotient.mk_zero _

theorem LeafTwPt_of (hA : LeafTwAdj) (hG : LeafTwGen) (hF : LeafTwFieldZ) : LeafTwPt := by
  intro q _ j U u t V g v hgv ht
  by_cases hq : IsUnit (q : Γ(U, ⊤))
  swap
  · refine ⟨U, 𝟙 U, inferInstance, ⟨u, rfl⟩, ?_⟩
    rw [twF_eq_zero_of_not_unit j hq t]; exact map_zero _
  obtain ⟨W₁, w₁, hw₁, ⟨w, hw⟩, ⟨ζ⟩⟩ := hA q U u hq
  haveI := hw₁
  obtain ⟨O, c, hwO, hO⟩ := hG q j W₁ ζ (((twF q j).map (Scheme.Γ.map w₁.op)).hom t) w
  have hO' : ((twF q j).map (Scheme.Γ.map (O.ι ≫ w₁).op)).hom t =
      ULift.up c • twCls j (ζ.map (Scheme.Γ.map O.ι.op).hom) := by
    rw [twF_res_comp, hO]; exact twF_map_cls j _ ζ c
  obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := O.ι ≫ w₁) (g := g)
    (⟨w, hwO⟩ : O.toScheme) v (by rw [hgv]; exact hw)
  have hc : c = 0 := by
    let P := pullback (O.ι ≫ w₁) g
    let φ := P.evaluation ⊤ p trivial
    have e : ((twF q j).map (Scheme.Γ.map (pullback.fst (O.ι ≫ w₁) g ≫ O.ι ≫ w₁).op)).hom t = 0 := by
      rw [pullback.condition, twF_res_comp, ht, map_zero]
    rw [twF_res_comp, hO', twF_map_cls] at e
    have key := twF_map_cls j φ (Prim.map (Scheme.Γ.map (pullback.fst (O.ι ≫ w₁) g).op).hom
      (Prim.map (Scheme.Γ.map O.ι.op).hom ζ)) c
    exact hF q j (P.residueField p) (Field.toIsField _) _ c
      (key.symm.trans ((congrArg (fun x => ((twF q j).map φ).hom x) e).trans (map_zero _)))
  refine ⟨O, O.ι ≫ w₁, inferInstance, ⟨⟨w, hwO⟩, hw⟩, ?_⟩
  rw [hO', hc]
  exact zero_smul (ULift (ZMod q)) _

end LateralTheory.E.E8.TwSec
end
end

