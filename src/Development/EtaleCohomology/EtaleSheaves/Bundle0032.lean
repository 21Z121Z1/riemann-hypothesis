import Development.EtaleCohomology.EtaleSheaves.EqvOfCompRight
import Development.EtaleCohomology.EtaleSheaves.Bundle0022
import Development.EtaleCohomology.EtaleSheaves.Bundle0017
import Development.EtaleCohomology.TateTwists.Bundle0014
import Development.EtaleCohomology.EtaleSheaves.Bundle0028
import Development.EtaleCohomology.EtaleSheaves.Bundle0016
import Development.EtaleCohomology.EtaleSheaves.Bundle0024

-- bundled from Development.EtaleCohomology.EtaleSheaves.CechSigmaOf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechSigma_xy1Pf_Lev
open LateralTheory.E.CechSigmaProof

def sqS {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O) :
    Arrow.mk (cov (g ⁻¹ᵁ O) (fun j => g ⁻¹ᵁ V j) (fun j => pre_le g (hV j))) ⟶ Arrow.mk (cov O V hV) :=
  Arrow.homMk (Limits.Sigma.map fun j => g ∣_ V j) (g ∣_ O) (sq_cov g O V hV)

def wpMap {A B C D : Scheme.{0}} {p : A ⟶ B} {q : C ⟶ D} (s : Arrow.mk p ⟶ Arrow.mk q) (n : ℕ) :
    widePullback B (fun _ : Fin (n + 1) => A) (fun _ => p) ⟶ widePullback D (fun _ : Fin (n + 1) => C) (fun _ => q) :=
  WidePullback.lift (WidePullback.base _ ≫ s.right) (fun i => WidePullback.π _ i ≫ s.left)
    (fun i => by have := Arrow.w s; simp only [Arrow.mk_hom] at this; simp [this])

def CechYoneda : Prop := ∀ {A B C D : Scheme.{0}} {p : A ⟶ B} {q : C ⟶ D} (s : Arrow.mk p ⟶ Arrow.mk q) (n : ℕ),
  Nonempty (Arrow.mk ((Arrow.mapCechNerve (yoneda.mapArrow.map s)).app (op (SimplexCategory.mk n))) ≅
    Arrow.mk (yoneda.map (wpMap s n)))

def SchemeLevel : Prop := ∀ {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens) {ι : Type} (V : ι → X.Opens) (hV : ∀ j, V j ≤ O)
  (n : ℕ), Nonempty (Arrow.mk (wpMap (sqS g O V hV) n) ≅
    Arrow.mk (Limits.Sigma.map fun j : Fin (n + 1) → ι => g ∣_ (⨅ k, V (j k))))

theorem LevelIso_of (hY : CechYoneda) (hS : SchemeLevel) : LevelIso := by
  intro Y X g O ι V hV n
  obtain ⟨e1⟩ := hY (sqS g O V hV) n
  obtain ⟨e2⟩ := hS g O V hV n
  exact ⟨e1 ≪≫ yoneda.mapArrow.mapIso e2⟩

theorem CechSigma_of (hY : CechYoneda) (hS : SchemeLevel) : ZariskiLocalCech.CechSigma :=
  LateralTheory.E.CechSigmaProof.CechSigma_of (LevelIso_of hY hS)

end LateralTheory.E.CechSigma_xy1Pf_Lev
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChartAwayPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.ChartAwayPf

theorem ChartAway_of : LateralTheory.E.LeafChartAffPf.ChartAway := by
  intro X Y B _ j _ I g hj
  let f := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away g)))
  have hf : ∀ y' : Spec (CommRingCat.of (Localization.Away g)),
      (show PrimeSpectrum B from f.base y') =
        PrimeSpectrum.comap (algebraMap B (Localization.Away g)) (show PrimeSpectrum _ from y') := fun _ => rfl
  refine ⟨f ≫ j, inferInstance, ?_, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨f.base y, rfl⟩
  · intro y hy
    have : (show PrimeSpectrum B from y) ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away g))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
      exact hy
    obtain ⟨y', hy'⟩ := this
    refine ⟨y', ?_⟩
    show j.base (f.base y') = j.base y
    rw [show f.base y' = y from (hf y').trans hy']
  · intro y'
    show j.base (f.base y') ∈ Y ↔ _
    rw [hj (f.base y'), hf y', Ideal.map_le_iff_le_comap]
    rfl

end LateralTheory.E.ChartAwayPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChartGeoGlue
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.ChartGeoPf

def ChartStdGeo : Prop := ∀ {X S : Scheme.{0}} (p : X ⟶ S) (n : ℕ) [SmoothOfRelativeDimension n p] (x : X)
  (W : X.Opens), x ∈ W → ∃ (U : S.Opens) (_ : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (hUV : V ≤ p ⁻¹ᵁ U), x ∈ V ∧ V ≤ W ∧ (p.appLE U V hUV).hom.IsStandardSmoothOfRelativeDimension n

def RangeKer : Prop := ∀ {X Z : Scheme.{0}} (ι : Z ⟶ X) [IsClosedImmersion ι] (V : X.Opens) (hV : IsAffineOpen V)
  (y : Spec Γ(X, V)), hV.fromSpec y ∈ Set.range ι ↔ RingHom.ker (ι.app V).hom ≤ (show PrimeSpectrum Γ(X, V) from y).asIdeal

def QuotLoc : Prop := ∀ (n : ℕ) (A B T : Type) [CommRing A] [CommRing B] [CommRing T] [Algebra A B] (π : B →+* T),
  Function.Surjective π → RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (π.comp (algebraMap A B)) →
  ∀ P : Ideal B, P.IsPrime → RingHom.ker π ≤ P → ∃ g ∉ P,
    Algebra.IsStandardSmoothOfRelativeDimension n A (Localization.Away g ⧸ (RingHom.ker π).map (algebraMap B (Localization.Away g)))

end LateralTheory.E.ChartGeoPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChernClassRootLocalization
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernClassRootLocalization

open LateralTheory.E.CupProductRingLaws LateralTheory.E.ChernCocycleExistenceAndUniqueness

theorem sec_sep {R : Type} [CommRing R] (F : Shv R) (U : Scheme.{0}) (a b : Sec F U)
    (h : Loc U fun _ g => Sec.res g a = Sec.res g b) : a = b := by
  obtain ⟨S, hS, hab⟩ := h
  have hF := ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).cond
  rw [isSheaf_iff_isSheaf_of_type] at hF
  exact (hF S hS).isSeparatedFor.ext (fun V g hg => hab V g hg)

variable {R : Type} [CommRing R] in
theorem freeGen_res (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    freeGen R P V (P.map g.op x) = Sec.res g (freeGen R P U x) := by
  have key := NatTrans.naturality_apply (toSheafify Scheme.etaleTopology ((freeP R).obj P)) g.op
    (ModuleCat.freeMk (R := ULift.{1} R) (show uliftFunctor.{1, 0}.obj (P.obj (op U)) from ULift.up x))
  refine Eq.trans ?_ key
  unfold freeGen
  congr 1
  simp only [freeP, Functor.whiskeringRight_obj_obj, Functor.comp_map]
  erw [ModuleCat.free_map_apply]
  rfl

variable {R : Type} [CommRing R] in
theorem ev_res {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
    {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) : ev α p s h V (x.res g) = Sec.res g (ev α p s h U x) := by
  unfold ev Sx.res
  rw [freeGen_res]
  exact NatTrans.naturality_apply (((chainsXIso R E p).inv ≫ α.v _ _ h).hom) g.op _

def LeafRootLoc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ,
  Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u

theorem evUnique_of (hr : LeafRootLoc) : EtaleKummerChernCocycleEvaluationsUnique := by
  intro q _ E L hq γ γ' h h'
  constructor
  · intro U x
    apply sec_sep
    refine LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_imp (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hq U x) fun V g hv => ?_
    obtain ⟨v, hv⟩ := hv
    rw [← ev_res, ← ev_res, h.2.1 V _ v hv, h'.2.1 V _ v hv]
  · intro U x
    apply sec_sep
    refine LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_imp (LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_and (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hq U (x.sub 0 1 (by omega)))
      (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hq U (x.sub 1 1 (by omega)))) fun V g hv => ?_
    obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := hv
    rw [← LateralTheory.EtaleFoundations.FirstChernUniqueness.sub_res] at hv hw
    rw [← ev_res, ← ev_res, h.2.2 V _ v w hv hw, h'.2.2 V _ v w hv hw]

theorem etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique (hE : EtaleKummerChernCocycleExists) (hr : LeafRootLoc) : EtaleFirstChernClassRepresentedByChernCocycle :=
  LateralTheory.E.ChernCocycleExistenceAndUniqueness.etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique hE (evUnique_of hr)

end LateralTheory.E.ChernClassRootLocalization
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChowGraphCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.ChowLCut

namespace LateralTheory.E.ChowGraphCut

theorem iterLine_isProper {P S : Scheme.{0}} {q : P ⟶ S} (h : IterLine q) : IsProper q := by
  induction h with
  | iso e he => exact inferInstance
  | comp l k hl _ ih =>
    have := hl.1
    exact inferInstance

def Cover : Prop := ∀ (A : Type) [CommRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact p],
  Nonempty X → ∃ (n : ℕ) (U : Fin n → X.Opens), (∀ j, IsAffineOpen (U j)) ∧ (∀ j, (U j : Set X).Nonempty) ∧
    ∀ x : X, ∃ j, x ∈ U j

def Embed : Prop := ∀ (A : Type) [CommRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType p]
  (V : X.Opens), IsAffineOpen V → ∃ (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of A)) (W : P.Opens)
    (e : V.toScheme ⟶ W.toScheme), IterLine q ∧ IsClosedImmersion e ∧ e ≫ W.ι ≫ q = V.ι ≫ p

def IterComp : Prop := ∀ {P T S : Scheme.{0}} (l : P ⟶ T) (k : T ⟶ S), IterLine l → IterLine k → IterLine (l ≫ k)

def Prod : Prop := ∀ {S : Scheme.{0}} (n : ℕ) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S), (∀ j, IterLine (qj j)) →
  ∃ (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j), IterLine q ∧ (∀ j, π j ≫ qj j = q) ∧
    ∀ {T : Scheme.{0}} (t : T ⟶ S) (f : ∀ j, T ⟶ Pj j), (∀ j, f j ≫ qj j = t) →
      ∃! g : T ⟶ P, g ≫ q = t ∧ ∀ j, g ≫ π j = f j

def Core : Prop := ∀ {S X₁ : Scheme.{0}} (p₁ : X₁ ⟶ S) [IsProper p₁], IsIntegral X₁ →
  ∀ (n : ℕ) (U : Fin n → X₁.Opens) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S) (W : ∀ j, (Pj j).Opens)
    (e : ∀ j, (U j).toScheme ⟶ (W j).toScheme) (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j),
    (∀ j, (U j : Set X₁).Nonempty) → (∀ x : X₁, ∃ j, x ∈ U j) → (∀ j, IsSeparated (qj j)) →
    (∀ j, IsClosedImmersion (e j)) → (∀ j, e j ≫ (W j).ι ≫ qj j = (U j).ι ≫ p₁) → (∀ j, π j ≫ qj j = q) →
    (∀ {T : Scheme.{0}} (t : T ⟶ S) (f : ∀ j, T ⟶ Pj j), (∀ j, f j ≫ qj j = t) →
      ∃! g : T ⟶ P, g ≫ q = t ∧ ∀ j, g ≫ π j = f j) →
    ∃ (X' : Scheme.{0}) (i : X' ⟶ pullback p₁ q) (V : X₁.Opens) (s : V.toScheme ⟶ X'),
      IsClosedImmersion i ∧ IsClosedImmersion (i ≫ pullback.snd p₁ q) ∧ (V : Set X₁).Nonempty ∧
      s ≫ i ≫ pullback.fst p₁ q = V.ι

theorem goal_of (hC : Cover) (hE : Embed) (hP : Prod) (hK : Core) : ChowGraph := by
  intro A _ X₁ p₁ _ hX
  have := hX
  obtain ⟨n, U, hUa, hUn, hUc⟩ := hC A p₁ inferInstance
  choose Pj qj W e hq he hc using fun j => hE A p₁ (U j) (hUa j)
  obtain ⟨P, q, π, hq', hπ, hUP⟩ := hP n Pj qj hq
  have hsep : ∀ j, IsSeparated (qj j) := fun j => by
    have := iterLine_isProper (hq j)
    infer_instance
  obtain ⟨X', i, V, s, h1, h2, h3, h4⟩ := hK p₁ hX n U Pj qj W e P q π hUn hUc hsep he hc hπ hUP
  exact ⟨P, q, X', i, V, s, hq', h1, h2, h3, h4⟩

end LateralTheory.E.ChowGraphCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ClsBiprodEqZero
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.BinPf

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

theorem cls_biprod_eq_zero {K₁ K₂ L : CochainComplex C ℤ} {n : ℤ} (x : CohomologyClass (K₁ ⊞ K₂) L n)
    (h₁ : cpre (Cocycle.ofHom (biprod.inl : K₁ ⟶ K₁ ⊞ K₂)) L n n (zero_add n) x = 0)
    (h₂ : cpre (Cocycle.ofHom (biprod.inr : K₂ ⟶ K₁ ⊞ K₂)) L n n (zero_add n) x = 0) : x = 0 := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  rw [cpre_mk, CohomologyClass.mk_eq_zero_iff] at h₁ h₂
  obtain ⟨m, hm, β₁, hβ₁⟩ := h₁
  obtain ⟨m', hm', β₂, hβ₂⟩ := h₂
  have hmm : m' = m := by omega
  subst hmm
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m', hm', (Cochain.ofHom (biprod.fst : K₁ ⊞ K₂ ⟶ K₁)).comp β₁ (zero_add m') +
    (Cochain.ofHom (biprod.snd : K₁ ⊞ K₂ ⟶ K₂)).comp β₂ (zero_add m'), ?_⟩
  rw [δ_add, δ_ofHom_comp, δ_ofHom_comp, hβ₁, hβ₂]
  change (Cochain.ofHom (biprod.fst : K₁ ⊞ K₂ ⟶ K₁)).comp ((Cochain.ofHom biprod.inl).comp α.1 (zero_add n)) (zero_add n) +
    (Cochain.ofHom (biprod.snd : K₁ ⊞ K₂ ⟶ K₂)).comp ((Cochain.ofHom biprod.inr).comp α.1 (zero_add n)) (zero_add n) = α.1
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.add_comp, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, ← Cochain.ofHom_add, biprod.total,
    Cochain.id_comp]

theorem hkpull_comp {R : Type} [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [HK.pull, HK.pre, cpre_mk, zcomp, Cochain.ofHom_comp]

theorem hkpull_id {R : Type} [CommRing R] {K : Cx R} (F : Shv R) (n : ℤ)
    (x : HK R K F n) : HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [HK.pull, HK.pre, cpre_mk, zcomp]

def ChainsCoprod : Prop := ∀ (R : Type) [CommRing R] (U V : Spc),
  IsIso (biprod.desc ((chains R).map (coprod.inl : U ⟶ U ⨿ V)) ((chains R).map (coprod.inr : V ⟶ U ⨿ V)))

def CoprodAcyc : Prop := ∀ (q : ℕ) (U V : Spc), Acyc q U → Acyc q V → Acyc q (U ⨿ V)

theorem coprodAcyc_of (hC : ChainsCoprod) : CoprodAcyc := by
  intro q U V hU hV n i hn
  have hI := hC (ZMod q) U V
  set φ := biprod.desc ((chains (ZMod q)).map (coprod.inl : U ⟶ U ⨿ V)) ((chains (ZMod q)).map (coprod.inr : V ⟶ U ⨿ V))
  have h0 : ∀ x : Ht q (U ⨿ V) n i, x = 0 := by
    intro x
    have hy : HK.pull _ φ _ n x = 0 := by
      apply cls_biprod_eq_zero
      · have e := hkpull_comp (biprod.inl) φ (tw q i) n x
        rw [biprod.inl_desc] at e
        have : HK.pull _ ((chains (ZMod q)).map (coprod.inl : U ⟶ U ⨿ V)) (tw q i) n x = 0 :=
          (hU n i hn).elim _ _
        rw [this] at e
        exact e.symm
      · have e := hkpull_comp (biprod.inr) φ (tw q i) n x
        rw [biprod.inr_desc] at e
        have : HK.pull _ ((chains (ZMod q)).map (coprod.inr : V ⟶ U ⨿ V)) (tw q i) n x = 0 :=
          (hV n i hn).elim _ _
        rw [this] at e
        exact e.symm
    have e := hkpull_comp (inv φ) φ (tw q i) n x
    rw [IsIso.inv_hom_id, hkpull_id, hy, map_zero] at e
    exact e
  exact ⟨fun x y => by rw [h0 x, h0 y]⟩

def DescEqv : Prop := LateralTheory.E.t_E2Cut.Hyp → ∀ (q : ℕ) (A R0 R1 : Type) [CommRing A] [CommRing R0] [CommRing R1]
  (e : A ≃+* R0 × R1) (i : ℤ),
  Eqv _ (coprod.desc (spMap ((RingHom.fst R0 R1).comp e.toRingHom)) (spMap ((RingHom.snd R0 R1).comp e.toRingHom))) (tw q i)

end LateralTheory.E.BinPf

theorem LateralTheory.E.ProdAcycPf.Bin_of (hD : LateralTheory.E.BinPf.DescEqv) (hC : LateralTheory.E.BinPf.ChainsCoprod) :
    LateralTheory.E.ProdAcycPf.Bin := by
  intro H q A R0 R1 _ _ _ ⟨e⟩ h0 h1 n i hn
  have hb := (hD H q A R0 R1 e i n).1
  have hs := LateralTheory.E.BinPf.coprodAcyc_of hC q _ _ h0 h1 n i hn
  exact ⟨fun x y => hb (Subsingleton.elim _ _)⟩
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CompCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut LateralTheory.E.BuildCut

namespace LateralTheory.E.CompCut

def LocAC : Prop := ∀ (W : Type) [CommRing W], ProdACF W → ∀ q : PrimeSpectrum W,
  IsField (Localization.AtPrime q.asIdeal) ∧ AIC (Localization.AtPrime q.asIdeal)

def NormAC : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (K : Type) [CommRing K], IsField K → AIC K → ∀ v : Spec (CommRingCat.of K) ⟶ P,
  AICSch v.normalization

def Sys : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (q : PrimeSpectrum W) (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D)
      (ι : ∀ j, D.obj j ⟶ w.normalization), ClopenSys y D c ι ∧
      Nonempty (c.pt ≅ (Spec.map (CommRingCat.ofHom (algebraMap W (Localization.AtPrime q.asIdeal))) ≫ w).normalization)

theorem goal_of (hS : Sys) (hL : LocAC) (hN : NormAC) : Comp := by
  intro P _ _ W _ w hW y
  obtain ⟨q, J, _, _, D, c, ι, hc, ⟨e⟩⟩ := hS W w hW y
  obtain ⟨hF, hA⟩ := hL W hW q
  refine ⟨J, inferInstance, inferInstance, D, c.extend e.inv, ι, ⟨⟨IsLimit.ofIsoLimit hc.1.some (Cone.extendIso c e)⟩,
    hc.2.1, hc.2.2⟩, ?_⟩
  exact hN _ hF hA _

end LateralTheory.E.CompCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DiagramChase
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf

namespace LateralTheory.E.StepSPf

def PO (q : ℕ) {J : Type} [SmallCategory J] (D : J ⥤ Scheme.{0}) (c : Cone D) (j0 : J) (W : (D.obj j0).Opens) : Prop :=
  ∀ n i : ℤ,
  (∀ x : Ht q (sch.obj (c.π.app j0 ⁻¹ᵁ W).toScheme) n i, ∃ (k : J) (f : k ⟶ j0)
      (y : Ht q (sch.obj (D.map f ⁻¹ᵁ W).toScheme) n i),
      pull _ (sch.map ((c.π.app k).resLE (D.map f ⁻¹ᵁ W) (c.π.app j0 ⁻¹ᵁ W)
        (by rw [← Scheme.Hom.comp_preimage, c.w]))) _ _ y = x) ∧
  ∀ (k : J) (f : k ⟶ j0) (y : Ht q (sch.obj (D.map f ⁻¹ᵁ W).toScheme) n i),
    pull _ (sch.map ((c.π.app k).resLE (D.map f ⁻¹ᵁ W) (c.π.app j0 ⁻¹ᵁ W)
        (by rw [← Scheme.Hom.comp_preimage, c.w]))) _ _ y = 0 →
    ∃ (l : J) (g : l ⟶ k), pull _ (sch.map ((D.map g).resLE (D.map f ⁻¹ᵁ W) (D.map (g ≫ f) ⁻¹ᵁ W)
        (by rw [← Scheme.Hom.comp_preimage, ← D.map_comp]))) _ _ y = 0

def Restr : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ (j0 : J) (X : Scheme.{0}) (e : D.obj j0 ≅ X)
  (W : X.Opens), IsCompact (W : Set X) → PC W.toScheme → PO q D c j0 (e.hom ⁻¹ᵁ W)

def DiagramChase₂ : Prop := Hyp → MV → ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ (j0 : J) (X : Scheme.{0}) (e : D.obj j0 ≅ X)
  (U V : X.Opens), U ⊔ V = ⊤ → PO q D c j0 (e.hom ⁻¹ᵁ U) → PO q D c j0 (e.hom ⁻¹ᵁ V) → PO q D c j0 (e.hom ⁻¹ᵁ (U ⊓ V)) →
  ∀ n i : ℤ, ∀ x : Ht q (sch.obj c.pt) n i, ∃ j y, pull _ (sch.map (c.π.app j)) _ _ y = x

theorem S_of_restr_chase (hR : Restr) (hC : DiagramChase₂) : LateralTheory.E.ContStepPf.StepS := by
  intro h hmv X U V hU hV hUV pU pV pW q J _ _ D c hc ha hcs hqs hu j0 ⟨e⟩ n i
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated e.inv
  have hW : IsCompact ((U ⊓ V : X.Opens) : Set X) := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact QuasiSeparatedSpace.inter_isCompact _ _ U.2 hU V.2 hV
  exact hC h hmv q D c hc ha hcs hqs hu j0 X e U V hUV (hR q D c hc ha hcs hqs hu j0 X e U hU pU)
    (hR q D c hc ha hcs hqs hu j0 X e V hV pV) (hR q D c hc ha hcs hqs hu j0 X e (U ⊓ V) hW pW) n i

theorem po_res_zero {q : ℕ} {Y Z : Scheme.{0}} (φ : Y ⟶ Z) (A : Z.Opens) (B B' : Y.Opens) (hB : B = B')
    (h : B ≤ φ ⁻¹ᵁ A) (h' : B' ≤ φ ⁻¹ᵁ A) (n i : ℤ) (y : Ht q (sch.obj A.toScheme) n i) :
    pull _ (sch.map (φ.resLE A B h)) _ _ y = 0 → pull _ (sch.map (φ.resLE A B' h')) (tw q i) n y = 0 := by
  subst hB; exact id

theorem restr : Restr := by
  intro q J _ _ D c hc ha hcs hqs hu j0 X e W hWc pW
  have : ∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f) := ha
  set W' : (D.obj j0).Opens := e.hom ⁻¹ᵁ W with hW'def
  have hW' : IsCompact (W' : Set (D.obj j0)) := QuasiCompact.isCompact_preimage (f := e.hom) _ W.2 hWc
  have key := pW q (opensDiagram D j0 W') (opensCone D c j0 W') (isLimitOpensCone D c hc j0 W')
    (fun f => inferInstance)
    (fun j => isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := D.map j.hom) _ W'.2 hW'))
    (fun j => by have := hqs j.left; exact (D.map j.hom ⁻¹ᵁ W').ι.isOpenEmbedding.quasiSeparatedSpace)
    (fun j => by
      have h := (hu j.left).map ((D.map j.hom ⁻¹ᵁ W').ι.appTop.hom)
      simp only [map_natCast] at h
      exact h)
    (Over.mk (𝟙 j0)) ⟨(Scheme.isoOfEq _ (by simp [hW'def])) ≪≫ e.hom.preimageIso W⟩
  intro n i
  refine ⟨fun x => ?_, fun k f y hy => ?_⟩
  · obtain ⟨j, y, hy⟩ := (key n i).1 x
    exact ⟨j.left, j.hom, y, hy⟩
  · obtain ⟨k', g, hg⟩ := (key n i).2 (Over.mk f) y hy
    have hw : g.left ≫ f = k'.hom := Over.w g
    refine ⟨k'.left, g.left, ?_⟩
    exact po_res_zero (D.map g.left) _ _ _ (by rw [hw]) _ _ n i y hg

end LateralTheory.E.StepSPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DiscLvlPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.DiscLvlPf

variable (R : Type) [CommRing R]

def e0 (E : Spc) : ((chains R).obj E).X 0 ≅ (free R).obj (E.obj (op (SimplexCategory.mk 0))) :=
  ((chainsN R).obj E).extendXIso ComplexShape.embeddingDownNat (i := 0) rfl

theorem etale_discrete_chains_degree_zero_iso_free_naturality {E E' : Spc} (g : E ⟶ E') :
    ((chains R).map g).f 0 ≫ (e0 R E').hom = (e0 R E).hom ≫ (free R).map (g.app (op (SimplexCategory.mk 0))) := by
  have : ((chains R).map g).f 0 = (e0 R E).hom ≫ ((chainsN R).map g).f 0 ≫ (e0 R E').inv :=
    HomologicalComplex.extendMap_f (φ := (chainsN R).map g) (e := ComplexShape.embeddingDownNat) (i := 0) (i' := 0) rfl
  rw [this]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem d_zero (P : PSh) : ((chains R).obj (disc.obj P)).d (-1) 0 = 0 := by
  change (HomologicalComplex.extend ((chainsN R).obj (disc.obj P)) ComplexShape.embeddingDownNat).d (-1) 0 = 0
  rw [HomologicalComplex.extend_d_eq (K := (chainsN R).obj (disc.obj P)) (e := ComplexShape.embeddingDownNat) (i' := -1) (j' := 0) (i := 1) (j := 0) rfl rfl]
  have : ((chainsN R).obj (disc.obj P)).d 1 0 = 0 := by
    change (AlgebraicTopology.AlternatingFaceMapComplex.obj (((SimplicialObject.whiskering _ _).obj (free R)).obj (disc.obj P))).d (0 + 1) 0 = 0
    have h01 : (((SimplicialObject.whiskering _ _).obj (free R)).obj (disc.obj P)).δ (0 : Fin 2) =
      (((SimplicialObject.whiskering _ _).obj (free R)).obj (disc.obj P)).δ (1 : Fin 2) := rfl
    rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq, Fin.sum_univ_two, h01]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul, add_neg_cancel]
  rw [this, zero_comp, comp_zero]

def e0d (P : PSh) : ((chains R).obj (disc.obj P)).X 0 ≅ (free R).obj P := e0 R (disc.obj P)

@[reassoc]
theorem etale_discrete_simplicial_chains_degree_zero_iso_naturality {P Q : PSh} (h : P ⟶ Q) :
    ((chains R).map (disc.map h)).f 0 ≫ (e0d R Q).hom = (e0d R P).hom ≫ (free R).map h :=
  etale_discrete_chains_degree_zero_iso_free_naturality R (disc.map h)

def pr (P : PSh) : (chains R).obj (disc.obj P) ⟶ (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj P) :=
  HomologicalComplex.mkHomToSingle (e0d R P).hom (fun i hi => by
    have hi' : i = -1 := by simp at hi; omega
    subst hi'
    rw [d_zero, zero_comp])

def sec (P : PSh) : (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj ((free R).obj P) ⟶ (chains R).obj (disc.obj P) :=
  HomologicalComplex.mkHomFromSingle (e0d R P).inv (fun k hk =>
    (LateralTheory.E.CechFiltPf.chains_isZero R (disc.obj P) k (by simp at hk; omega)).eq_of_tgt _ _)

theorem sec_pr (P : PSh) : sec R P ≫ pr R P = 𝟙 _ := by
  ext
  simp [sec, pr]

theorem pr_comm {P Q : PSh} (h : P ⟶ Q) :
    (chains R).map (disc.map h) ≫ pr R Q = pr R P ≫ (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map h) := by
  ext
  simp [pr, etale_discrete_simplicial_chains_degree_zero_iso_naturality_assoc, HomologicalComplex.single_map_f_self]

theorem sec_comm {P Q : PSh} (h : P ⟶ Q) :
    (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map h) ≫ sec R Q = sec R P ≫ (chains R).map (disc.map h) := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, sec, HomologicalComplex.mkHomFromSingle_f, HomologicalComplex.single_map_f_self,
    Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  rw [Iso.eq_inv_comp, ← etale_discrete_simplicial_chains_degree_zero_iso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

theorem cone_map_congr {K₁ L₁ K₂ L₂ : Cx R} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) {a a' : K₁ ⟶ K₂} {b b' : L₁ ⟶ L₂}
    (c : φ₁ ≫ b = a ≫ φ₂) (c' : φ₁ ≫ b' = a' ≫ φ₂) (ha : a = a') (hb : b = b') :
    mappingCone.map φ₁ φ₂ a b c = mappingCone.map φ₁ φ₂ a' b' c' := by
  subst ha hb; rfl

theorem pull_comp' {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem pull_id' (K : Cx R) (F : Shv R) (n : ℤ) (x : HK R K F n) : HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

end LateralTheory.E.DiscLvlPf

open LateralTheory.E.DiscLvlPf in
theorem LateralTheory.E.DiscLvlPf.DiscLvl_of : LateralTheory.E.CechFiltPf.DiscLvl := by
  intro R _ F P Q h m hs
  let φ₁ := (chains R).map (disc.map h)
  let φ₂ := (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map h)
  let Pm := mappingCone.map φ₁ φ₂ (pr R P) (pr R Q) (pr_comm R h)
  let Sm := mappingCone.map φ₂ φ₁ (sec R P) (sec R Q) (sec_comm R h)
  have hSP : Sm ≫ Pm = 𝟙 _ := by
    rw [← mappingCone.map_comp]
    rw [cone_map_congr R φ₂ φ₂ _ (by rw [Category.id_comp, Category.comp_id]) (sec_pr R P) (sec_pr R Q)]
    exact mappingCone.map_id φ₂
  have : Subsingleton (HK R (mappingCone φ₁) F m) := hs
  refine Function.Injective.subsingleton (f := HK.pull R Pm F m) ?_
  intro x y hxy
  have := congrArg (HK.pull R Sm F m) hxy
  rwa [← pull_comp', ← pull_comp', hSP, pull_id', pull_id'] at this
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LSecGluePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.L_sec_gluePf

theorem typeSheaf {R : Type} [CommRing R] (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).cond

end LateralTheory.E.L_sec_gluePf
end
end

