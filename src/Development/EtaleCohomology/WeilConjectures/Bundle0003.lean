import Development.EtaleCohomology.WeilConjectures.Bundle0002

-- bundled from Development.EtaleCohomology.WeilConjectures.GlueOfSig
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.EWeil.Gys.LV.GluePf

theorem shvSigma : ShvSigma := by
  intro R _ F T Y c hc
  let G : Scheme.{0}ᵒᵖ ⥤ Type 1 := F.obj ⋙ forget _
  have hG : Presieve.IsSheaf Scheme.zariskiTopology G :=
    Presieve.isSheaf_of_le G Scheme.zariskiTopology_le_etaleTopology
      ((isSheaf_iff_isSheaf_of_type _ G).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget _)).1 F.property))
  have : PreservesLimitsOfShape (Discrete T) G := preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hG
  let hL : IsLimit (G.mapCone c.op) := isLimitOfPreserves G (Cofan.IsColimit.op hc)
  let e := Types.isLimitEquivSections hL
  have he : ∀ s t, (e s).1 ⟨t⟩ = GlobalTheory.EtC.Sec.res (c.inj t) s := fun s t => rfl
  constructor
  · intro s₁ s₂ h
    apply e.injective
    apply Subtype.ext
    funext ⟨t⟩
    rw [he, he]
    exact congrFun h t
  · intro y
    let sec : (Discrete.functor (fun a => op (Y a)) ⋙ G).sections :=
      ⟨fun j => y j.as, by
        rintro ⟨j⟩ ⟨j'⟩ ⟨⟨h⟩⟩
        cases h
        show G.map (𝟙 _) _ = _
        rw [G.map_id]; rfl⟩
    refine ⟨e.symm sec, ?_⟩
    funext t
    show GlobalTheory.EtC.Sec.res (c.inj t) (e.symm sec) = y t
    rw [← he, e.apply_symm_apply]

end LateralTheory.EWeil.Gys.LV.GluePf
end
end

-- bundled from Development.EtaleCohomology.WeilConjectures.PushPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.t_E3Cut (Et IE SHExists IEComp pC)
open LateralTheory.EWeil.ArtinCut LateralTheory.EWeil.LerayCut

namespace LateralTheory.EWeil.PushPf

abbrev bmap {A B : CommRingCat.{0}} (β : A ⟶ B) {W' W : (Spec A).Etale} (g : W' ⟶ W) :
    pullback W'.hom (Spec.map β) ⟶ pullback W.hom (Spec.map β) :=
  pullback.map _ _ _ _ g.left (𝟙 _) (𝟙 _) (by simp [MorphismProperty.Over.w g]) (by simp)

def LocCls (q : ℕ) {A B : CommRingCat.{0}} (β : A ⟶ B) (i : ℤ) (F : Sm A) (m : ℕ) : Prop :=
  ∀ (V : (Spec A).Etale) (s : F.obj.obj (op V)) (v : V.left),
    ∃ (W : (Spec A).Etale) (g : W ⟶ V) (w : W.left), g.left w = v ∧
      ∃ c : Ht q (sch.obj (pullback W.hom (Spec.map β))) (m : ℤ) i,
        ∀ (W' : (Spec A).Etale) (g' : W' ⟶ W) (w' : W'.left), g'.left w' = w →
          pull _ (sch.map (bmap β g')) _ _ c = 0 →
          ∃ (W'' : (Spec A).Etale) (g'' : W'' ⟶ W') (w'' : W''.left), g''.left w'' = w' ∧
            (F.obj.map (g'' ≫ g' ≫ g).op).hom s = 0

def PushCx : Prop := Base → ∀ (q : ℕ) [NeZero q] {A B : CommRingCat.{0}} (β : A ⟶ B), IsUnit (q : A) → ∀ i : ℤ,
  ∃ K : CochainComplex (Sm A) ℕ,
    (∀ s n : ℕ, 0 < n → Subsingleton (Sheaf.H.{1} (K.X s) n)) ∧
    (∀ (m : ℕ) (V : (Spec A).Etale) (x : (K.homology m).obj.obj (op V)), q • x = 0) ∧
    (∀ m : ℕ, LocCls q β i (K.homology m) m) ∧
    ∀ n : ℕ, Nonempty (Ht q (sch.obj (Spec B)) n i ≃ (gamCx (unitSh A) K).homology n)

def StalkLoc : Prop := Base → SHz → ∀ (q : ℕ) [NeZero q] {A B : CommRingCat.{0}} (β : A ⟶ B), IsUnit (q : A) →
  ∀ (i : ℤ) (m : ℕ) (p : PrimeSpectrum A),
    (∀ (S D : CommRingCat.{0}) (f : A ⟶ S) (u : B ⟶ D) (v : S ⟶ D), IsStalk f p → IsPushout β f u v → Van q D m) →
    ∀ (W : (Spec A).Etale) (w : W.left), W.hom w = p →
      ∀ c : Ht q (sch.obj (pullback W.hom (Spec.map β))) (m : ℤ) i,
        ∃ (W' : (Spec A).Etale) (g' : W' ⟶ W) (w' : W'.left), g'.left w' = w ∧
          pull _ (sch.map (bmap β g')) _ _ c = 0

end LateralTheory.EWeil.PushPf
end
end

