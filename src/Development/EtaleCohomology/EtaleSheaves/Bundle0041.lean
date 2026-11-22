import Development.EtaleCohomology.EtaleSheaves.Bundle0025
import Development.EtaleCohomology.EtaleSheaves.Bundle0016
import Development.EtaleCohomology.EtaleSheaves.Bundle0013
import Development.EtaleCohomology.EtaleSheaves.Bundle0022
import Development.EtaleCohomology.EtaleSheaves.Bundle0030
import Development.EtaleCohomology.EtaleSheaves.Bundle0021

-- bundled from Development.EtaleCohomology.EtaleSheaves.SheafPushoutSquare
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut LateralTheory.E.LeafExcPf LateralTheory.E.LeafSqPf

namespace LateralTheory.E.SheafPushoutSquare

theorem pushout_elem {R : Type} [CommRing R] {MA MB MC : PMod R} (a : MA ⟶ MB) (b : MA ⟶ MC) (T : Scheme.{0}ᵒᵖ)
    (z : (pushout a b).obj T) : ∃ (x : MB.obj T) (y : MC.obj T),
      ((pushout.inl a b).app T).hom x + ((pushout.inr a b).app T).hom y = z := by
  have hpo : IsPushout (a.app T) (b.app T) ((pushout.inl a b).app T) ((pushout.inr a b).app T) :=
    (IsPushout.of_hasPushout a b).map ((evaluation _ _).obj T)
  let P : Submodule (ULift.{1} R) ((pushout a b).obj T) :=
    LinearMap.range (((pushout.inl a b).app T).hom.coprod ((pushout.inr a b).app T).hom)
  let π : (pushout a b).obj T ⟶ ModuleCat.of _ (((pushout a b).obj T) ⧸ P) := ModuleCat.ofHom P.mkQ
  have h0 : π = 0 := by
    apply hpo.hom_ext
    · ext x
      exact (Submodule.Quotient.mk_eq_zero P).2 ⟨(x, 0), by simp <;> rfl⟩
    · ext y
      exact (Submodule.Quotient.mk_eq_zero P).2 ⟨(0, y), by simp <;> rfl⟩
  have hz : P.mkQ z = 0 := congrArg (fun f => f.hom z) h0
  obtain ⟨⟨x, y⟩, hxy⟩ := (Submodule.Quotient.mk_eq_zero P).1 hz
  exact ⟨x, y, by simpa using hxy⟩

theorem LeafSheafPush_pf : LeafSheafPush := by
  intro R _ MA MB MC MD a b c d w hon hker
  let φ := pushout.desc c d w
  have hinl : ∀ T x, (φ.app T).hom (((pushout.inl a b).app T).hom x) = (c.app T).hom x := fun T x => by
    change ((pushout.inl a b ≫ φ).app T).hom x = _
    rw [pushout.inl_desc]
  have hinr : ∀ T y, (φ.app T).hom (((pushout.inr a b).app T).hom y) = (d.app T).hom y := fun T y => by
    change ((pushout.inr a b ≫ φ).app T).hom y = _
    rw [pushout.inr_desc]
  have hs : Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} φ := by
    constructor
    intro T z
    obtain ⟨S, hS, hP⟩ := hon T z
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V k hk
    obtain ⟨x, y, hxy⟩ := hP V k hk
    refine ⟨((pushout.inl a b).app _).hom x + ((pushout.inr a b).app _).hom y, ?_⟩
    change (φ.app _).hom _ = _
    rw [map_add, hinl, hinr]
    exact hxy
  have hi : Presheaf.IsLocallyInjective Scheme.etaleTopology.{0} φ := by
    constructor
    intro T u v huv
    obtain ⟨x, y, hxy⟩ := pushout_elem a b T (u - v)
    have h0 : (c.app T).hom x + (d.app T).hom y = 0 := by
      rw [← hinl, ← hinr, ← map_add, hxy, map_sub]
      exact sub_eq_zero.2 huv
    obtain ⟨S, hS, hP⟩ := hker T.unop x y h0
    refine Scheme.etaleTopology.superset_covering ?_ hS
    intro V k hk
    obtain ⟨w', hw1, hw2⟩ := hP V k hk
    change ((pushout a b).map k.op).hom u = ((pushout a b).map k.op).hom v
    rw [← sub_eq_zero, ← map_sub, ← hxy, map_add]
    have n1 : ((pushout a b).map k.op).hom (((pushout.inl a b).app T).hom x) =
        ((pushout.inl a b).app _).hom ((MB.map k.op).hom x) := by
      change ((pushout.inl a b).app T ≫ (pushout a b).map k.op).hom x = _
      rw [← NatTrans.naturality]; rfl
    have n2 : ((pushout a b).map k.op).hom (((pushout.inr a b).app T).hom y) =
        ((pushout.inr a b).app _).hom ((MC.map k.op).hom y) := by
      change ((pushout.inr a b).app T ≫ (pushout a b).map k.op).hom y = _
      rw [← NatTrans.naturality]; rfl
    have hc : ((pushout.inl a b).app (op V)).hom ((a.app (op V)).hom w') =
        ((pushout.inr a b).app (op V)).hom ((b.app (op V)).hom w') := by
      change ((a ≫ pushout.inl a b).app (op V)).hom w' = ((b ≫ pushout.inr a b).app (op V)).hom w'
      rw [pushout.condition]
    have hy : (MC.map k.op).hom y = -(b.app (op V)).hom w' := by rw [hw2, neg_neg]
    rw [n1, n2, ← hw1, hy, map_neg, hc, add_neg_cancel]
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  have hW : Scheme.etaleTopology.{0}.W φ := Scheme.etaleTopology.W_of_isLocallyBijective φ
  have hiso : IsIso ((presheafToSheaf Scheme.etaleTopology.{0} _).map φ) := (GrothendieckTopology.W_iff _ φ).1 hW
  have h := (IsPushout.of_hasPushout a b).map (presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)))
  refine h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (asIso ((presheafToSheaf _ _).map φ)) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [asIso_hom, Iso.refl_hom, Category.id_comp, ← Functor.map_comp, φ, pushout.inl_desc]
  · simp only [asIso_hom, Iso.refl_hom, Category.id_comp, ← Functor.map_comp, φ, pushout.inr_desc]

end LateralTheory.E.SheafPushoutSquare
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ShiftLvlPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.ShiftLvlPf

universe u v

section General

variable {C : Type u} [Category.{v} C] [Abelian C]

def coneIso {A B A' B' : CochainComplex C ℤ} (φ : A ⟶ B) (ψ : A' ⟶ B') (e₁ : A ≅ A') (e₂ : B ≅ B')
    (h : φ ≫ e₂.hom = e₁.hom ≫ ψ) : mappingCone φ ≅ mappingCone ψ where
  hom := mappingCone.map φ ψ e₁.hom e₂.hom h
  inv := mappingCone.map ψ φ e₁.inv e₂.inv
    (by rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc])
  hom_inv_id := by
    rw [← mappingCone.map_comp]
    simp only [Iso.hom_inv_id]
    exact mappingCone.map_id φ
  inv_hom_id := by
    rw [← mappingCone.map_comp]
    simp only [Iso.inv_hom_id]
    exact mappingCone.map_id ψ

theorem sub_of_iso {K K' : CochainComplex C ℤ} (L : CochainComplex C ℤ) (n : ℤ) (e : K ≅ K')
    (h : Subsingleton (CohomologyClass K' L n)) : Subsingleton (CohomologyClass K L n) := by
  rw [(CohomologyClass.homAddEquiv (K := K) (L := L) (n := n)).toEquiv.subsingleton_congr]
  rw [(CohomologyClass.homAddEquiv (K := K') (L := L) (n := n)).toEquiv.subsingleton_congr] at h
  exact @Equiv.subsingleton _ _ ((((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapIso e).homCongr (Iso.refl ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L⟦n⟧))))) h

theorem sub_of_shift {A0 Ap : CochainComplex C ℤ} (I : CochainComplex C ℤ) (p n : ℤ) (e : Ap ≅ A0⟦p⟧)
    (h : Subsingleton (CohomologyClass A0 I (n - p))) : Subsingleton (CohomologyClass Ap I n) := by
  rw [(CohomologyClass.homAddEquiv (K := Ap) (L := I) (n := n)).toEquiv.subsingleton_congr]
  rw [(CohomologyClass.homAddEquiv (K := A0) (L := I) (n := n - p)).toEquiv.subsingleton_congr] at h
  let Q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let α : (Q.obj A0)⟦p⟧ ≅ Q.obj Ap := ((Q.commShiftIso p).app A0).symm ≪≫ Q.mapIso e.symm
  let β : (Q.obj (I⟦n - p⟧))⟦p⟧ ≅ Q.obj (I⟦n⟧) :=
    ((Q.commShiftIso p).app _).symm ≪≫ Q.mapIso ((CategoryTheory.shiftFunctorAdd' (CochainComplex C ℤ) (n - p) p n (by omega)).app I).symm
  have e1 := (Functor.FullyFaithful.ofFullyFaithful (CategoryTheory.shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) p)).homEquiv
    (X := Q.obj A0) (Y := Q.obj (I⟦n - p⟧))
  exact @Equiv.subsingleton _ _ (e1.trans (α.homCongr β)).symm h

def singleConeIso {X Y : C} (f : X ⟶ Y) (p : ℤ) :
    mappingCone ((HomologicalComplex.single C (ComplexShape.up ℤ) (-p)).map f) ≅
      (mappingCone ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map f))⟦p⟧ :=
  let σ := (CochainComplex.singleFunctors C).shiftIso p (-p) 0 (by omega)
  coneIso _ _ (σ.app X).symm (σ.app Y).symm (σ.inv.naturality f) ≪≫
    (mappingCone.shiftIso ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map f) p).symm

end General

theorem chains_f_comm (R : Type) [CommRing R] {E₀ E : Spc} (g : E₀ ⟶ E) (p : ℕ) :
    ((chains R).map g).f (-(p : ℤ)) ≫ (chainsXIso R E p).hom =
      (chainsXIso R E₀ p).hom ≫ (free R).map (g.app (op (SimplexCategory.mk p))) := by
  unfold chains chainsXIso
  rw [Functor.comp_map]
  show (HomologicalComplex.extendMap ((chainsN R).map g) ComplexShape.embeddingDownNat).f (ComplexShape.embeddingDownNat.f p) ≫
      (HomologicalComplex.extendXIso ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := p) rfl).hom =
    (HomologicalComplex.extendXIso ((chainsN R).obj E₀) ComplexShape.embeddingDownNat (i := p) rfl).hom ≫ _
  rw [HomologicalComplex.extendMap_f _ _ (i := p) rfl]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  congr 1

theorem ShiftLvl_of : LateralTheory.E.CechFiltPf.ShiftLvl := by
  intro R _ F E₀ E g p n h
  have h1 := sub_of_shift (res R F) (p : ℤ) n
    (singleConeIso ((free R).map (g.app (op (SimplexCategory.mk p)))) (p : ℤ)) h
  refine sub_of_iso (res R F) n ?_ h1
  exact coneIso _ _ ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).mapIso (chainsXIso R E₀ p))
    ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).mapIso (chainsXIso R E p))
    (by simp only [Functor.mapIso_hom, ← Functor.map_comp, chains_f_comm])

end LateralTheory.E.ShiftLvlPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StandardChartsLineOne
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut

namespace LateralTheory.E.StandardEtaleChartsMultivariableHensel

attribute [local instance] MvPolynomial.gradedAlgebra in

def stdOpen (i : Fin 2) : P1.Opens := Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (MvPolynomial.X i)

def StdPair {A : Type} [CommRing A] {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z) : Prop :=
  ∃ (L : Scheme.{0}) (u : Z ⟶ L) (l : L ⟶ Spec (CommRingCat.of A)) (f : L ⟶ P1), IsIntegralHom u ∧ IsProper l ∧
    IsPullback f l (terminal.from P1) (terminal.from _) ∧ u ≫ l = p ∧
    Set.range ι₁ = ((u ≫ f) ⁻¹ᵁ stdOpen 0 : Set Z) ∧ Set.range ι₂ = ((u ≫ f) ⁻¹ᵁ stdOpen 1 : Set Z)

def StdCharts : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p →
  ∃ (U V : Scheme.{0}) (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z), IsOpenImmersion ι₁ ∧ IsOpenImmersion ι₂ ∧ IsAffine U ∧ IsAffine V ∧
    Set.range ι₁ ∪ Set.range ι₂ = Set.univ ∧ StdPair p ι₁ ι₂

def MvHensel : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] (n : ℕ)
  (F : Fin n → MvPolynomial (Fin n) A) (x₀ : Fin n → A),
  (∀ i, MvPolynomial.eval x₀ (F i) ∈ IsLocalRing.maximalIdeal A) →
  IsUnit (MvPolynomial.eval x₀ (Matrix.det (Matrix.of fun i j => MvPolynomial.pderiv j (F i)))) →
  ∃ x : Fin n → A, (∀ i, MvPolynomial.eval x (F i) = 0) ∧ ∀ j, x j - x₀ j ∈ IsLocalRing.maximalIdeal A

def Heart : Prop := ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
  ∀ {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z → ∀ (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
  IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → IsAffine U → IsAffine V → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
  StdPair p ι₁ ι₂ →
  ∀ g : LocallyConstant ↥(pullback (fibMap p ι₁) (fibMap p ι₂)) (ZMod q),
    ∃ (a : LocallyConstant ↥(fib (ι₁ ≫ p)) (ZMod q)) (b : LocallyConstant ↥(fib (ι₂ ≫ p)) (ZMod q)),
      g = a.comap (pullback.fst (fibMap p ι₁) (fibMap p ι₂)).base.hom -
        b.comap (pullback.snd (fibMap p ι₁) (fibMap p ι₂)).base.hom

theorem chartSurj (hR : LateralTheory.E.ChartSurjCut.Root) (hL : LateralTheory.E.ChartSurjCut.LCIso) (hT : Heart) :
    ∀ (H : Hyp) (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
    ∀ {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z → ∀ (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
    IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → IsAffine U → IsAffine V → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
    StdPair p ι₁ ι₂ →
    ∀ w : Ht q (sch.obj (pullback (fibMap p ι₁) (fibMap p ι₂))) 0 i, ∃ a b,
      w = pull _ (sch.map (pullback.fst (fibMap p ι₁) (fibMap p ι₂))) (tw q i) 0 a -
        pull _ (sch.map (pullback.snd (fibMap p ι₁) (fibMap p ι₂))) (tw q i) 0 b := by
  unfold LateralTheory.E.ChartSurjCut.Root at hR
  unfold LateralTheory.E.ChartSurjCut.LCIso at hL
  intro H q i A _ _ hSH hq Z U V p hp hZ ι₁ ι₂ h1 h2 hU hV hcov hstd w
  obtain ⟨ζ⟩ := hR q A p hZ hq
  obtain ⟨e, he⟩ := hL H q i Z ζ
  have k1 : fibMap p ι₁ ≫ pullback.fst p (cpt A) = pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ := by rw [fibMap]; exact pullback.lift_fst _ _ _
  have k2 : fibMap p ι₂ ≫ pullback.fst p (cpt A) = pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂ := by rw [fibMap]; exact pullback.lift_fst _ _ _
  have eq : pullback.snd (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂ =
      pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁ := by
    rw [← k2, ← k1, ← Category.assoc, ← pullback.condition, Category.assoc]
  obtain ⟨a, b, hab⟩ := hT q A hSH hq p hp hZ ι₁ ι₂ h1 h2 hU hV hcov hstd
    ((e _ (pullback.fst (fibMap p ι₁) (fibMap p ι₂) ≫ pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁)).symm w)
  refine ⟨e _ (pullback.fst (ι₁ ≫ p) (cpt A) ≫ ι₁) a, e _ (pullback.fst (ι₂ ≫ p) (cpt A) ≫ ι₂) b, ?_⟩
  rw [he _ _ (pullback.fst (fibMap p ι₁) (fibMap p ι₂)) rfl, he _ _ (pullback.snd (fibMap p ι₁) (fibMap p ι₂)) eq,
    ← map_sub, ← hab, AddEquiv.apply_symm_apply]

theorem goal_of (hMV : MV) (hC : StdCharts) (hF : LateralTheory.E.LineOneCut.FibCover) (hA : ChartAcyc)
    (hR : LateralTheory.E.ChartSurjCut.Root) (hL : LateralTheory.E.ChartSurjCut.LCIso) (hT : Heart) : LineOne := by
  intro H q i A _ _ hSH hq Z p hp hZ
  obtain ⟨U, V, ι₁, ι₂, h1, h2, hU, hV, hcov, hstd⟩ := hC A p hp
  obtain ⟨hf1, hf2, hfcov⟩ := hF A p ι₁ ι₂ h1 h2 hcov
  obtain ⟨δ, hex, -⟩ := hMV H (ZMod q) (tw q i)
  have e := hex (fibMap p ι₁) (fibMap p ι₂) hfcov 0
  have aU := hA H q A p ι₁ h1 hU hZ hq
  have aV := hA H q A p ι₂ h2 hV hZ hq
  have key : ∀ x : Ht q (sch.obj (fib p)) 1 i, x = 0 := by
    intro x
    have s1 := aU 1 i one_pos
    have s2 := aV 1 i one_pos
    obtain ⟨w, hw⟩ := (e.2.2 x).1 ⟨@Subsingleton.elim _ s1 _ _, @Subsingleton.elim _ s2 _ _⟩
    obtain ⟨a, b, hab⟩ := chartSurj hR hL hT H q i A hSH hq p hp hZ ι₁ ι₂ h1 h2 hU hV hcov hstd w
    rw [← hw]
    exact (e.2.1 w).2 ⟨a, b, hab⟩
  exact ⟨fun x y => by rw [key x, key y]⟩

end LateralTheory.E.StandardEtaleChartsMultivariableHensel
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StandardChartsLineZero
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.StandardEtaleChartsIdempotentGluing

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

def mS (S : Subalgebra A K) : Submodule A K := IsLocalRing.maximalIdeal A • Subalgebra.toSubmodule S

def AdjoinInv (B : Subalgebra A K) (t : K) : Subalgebra A K := Algebra.adjoin A ((B : Set K) ∪ {t⁻¹})

structure Charts (B C : Subalgebra A K) (t : K) : Prop where
  ne : t ≠ 0
  tB : t ∈ B
  tC : t⁻¹ ∈ C
  intB : ∀ b ∈ B, IsIntegral (Algebra.adjoin A {t}) b
  intC : ∀ c ∈ C, IsIntegral (Algebra.adjoin A {t⁻¹}) c
  glue : AdjoinInv B t = Algebra.adjoin A ((C : Set K) ∪ {t})

def IdemPair (B C : Subalgebra A K) (t e f : K) : Prop :=
  e ∈ B ∧ f ∈ C ∧ e * e - e ∈ mS B ∧ f * f - f ∈ mS C ∧ e - f ∈ mS (AdjoinInv B t)

def StdCharts : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → AICSch Z →
  ∃ (K : Type) (_ : Field K) (_ : Algebra A K) (B C : Subalgebra A K) (t : K), Charts B C t ∧
    (∀ x ∈ B, x ∈ C → IsIntegral A x) ∧
    ∀ W : Set ↑(pullback p (cpt A)), IsClopen W → ∃ e f : K, IdemPair B C t e f ∧
      ((e ∈ mS B ∧ f ∈ mS C) → W = ∅) ∧ ((e - 1 ∈ mS B ∧ f - 1 ∈ mS C) → W = Set.univ)

def IdemLift : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] (K : Type) [Field K] [Algebra A K]
  (B C : Subalgebra A K) (t : K), Charts B C t → ∀ e f : K, IdemPair B C t e f →
  ∃ g ∈ B, g ∈ C ∧ g - e ∈ mS B ∧ g - f ∈ mS C

def AlgGlue : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] [HenselianLocalRing A] (K : Type) [Field K] [Algebra A K]
  (B C : Subalgebra A K) (t : K), Charts B C t → (∀ x ∈ B, x ∈ C → IsIntegral A x) → ∀ e f : K, IdemPair B C t e f →
  (e ∈ mS B ∧ f ∈ mS C) ∨ (e - 1 ∈ mS B ∧ f - 1 ∈ mS C)

theorem goal_of (hS : StdCharts) (hG : AlgGlue) : LateralTheory.E.t_E2Cut.LineZero := by
  intro A _ _ hSH Z p hIL hZ
  obtain ⟨hH, -⟩ := hSH
  have hne : Nonempty ↑(pullback p (cpt A)) := by
    obtain ⟨L, u, l, hu, hl, rfl⟩ := hIL
    have := hl.1
    have := hZ.1
    exact LateralTheory.E.LineZeroCut.lzNonempty A (u ≫ l) inferInstance inferInstance
  obtain ⟨K, _, _, B, C, t, hc, hint, hW⟩ := hS A p hIL hZ
  have hpre : PreconnectedSpace ↑(pullback p (cpt A)) := by
    rw [preconnectedSpace_iff_clopen]
    intro W hW'
    obtain ⟨e, f, hef, h0, h1⟩ := hW W hW'
    rcases hG A K B C t hc hint e f hef with h | h
    · exact Or.inl (h0 h)
    · exact Or.inr (h1 h)
  exact { toPreconnectedSpace := hpre, toNonempty := hne }

end LateralTheory.E.StandardEtaleChartsIdempotentGluing
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StrictHenselColimits
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.SHLocPf

namespace LateralTheory.E.ColimPf

def Absorb : Prop := ∀ (A : CommRingCat.{0}) (Ω : Type) [Field Ω] (ι : A →+* Ω),
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O) (ψ : O →+* Ω), IE f ∧ ψ.comp f.hom = ι ∧
    (∀ x : O, ψ x ≠ 0 → IsUnit x) ∧
    ∀ (B : CommRingCat.{0}) (g : A ⟶ B), Et g → ∀ φ : B →+* Ω, φ.comp g.hom = ι →
      ∃ h : B ⟶ O, g ≫ h = f ∧ ψ.comp h.hom = φ

def Rigid : Prop := ∀ (A B O : CommRingCat.{0}) (Ω : Type) [Field Ω] (ψ : O →+* Ω) (g : A ⟶ B), Et g →
  (∀ x : O, ψ x ≠ 0 → IsUnit x) → ∀ (u v : B ⟶ O), g ≫ u = g ≫ v → ψ.comp u.hom = ψ.comp v.hom → u = v

def Descend : Prop := ∀ (A O : CommRingCat.{0}) (f : A ⟶ O), IE f →
  ∀ (C : Type) [CommRing C] [Algebra O C] [Algebra.Etale O C],
  ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (d : B ⟶ O) (C' : CommRingCat.{0}) (e : B ⟶ C') (c : C' →+* C),
    Et g ∧ Et e ∧ g ≫ d = f ∧ c.comp e.hom = (algebraMap O C).comp d.hom ∧
    (∀ k : C' ⟶ O, e ≫ k = d → ∃ s : C →ₐ[O] O, s.toRingHom.comp c = k.hom) ∧
    (∀ (R : Type) [CommRing R] (α β : C →+* R), α.comp (algebraMap O C) = β.comp (algebraMap O C) →
      α.comp c = β.comp c → α = β)

theorem et_comp {A B C : CommRingCat.{0}} {g : A ⟶ B} {e : B ⟶ C} (hg : Et g) (he : Et e) : Et (g ≫ e) := by
  change (g ≫ e).hom.Etale
  rw [CommRingCat.hom_comp]
  exact RingHom.Etale.stableUnderComposition _ _ hg he

theorem Colim_of (hA : Absorb) (hR : Rigid) (hD : Descend) : Colim := by
  intro A Ω _ ι
  obtain ⟨O, f, ψ, hIE, hcomp, hloc, habs⟩ := hA A Ω ι
  refine ⟨O, f, ψ, hIE, hcomp, ?_⟩
  intro C _ _ _ χ hχ
  obtain ⟨B, g, d, C', e, c, hg, he, hgd, hce, hext, hgen⟩ := hD A O f hIE C
  have ce : ∀ y, c (e.hom y) = algebraMap O C (d.hom y) := fun y => DFunLike.congr_fun hce y
  have cχ : ∀ z, χ (algebraMap O C z) = ψ z := fun z => DFunLike.congr_fun hχ z
  have gd : ∀ x, d.hom (g.hom x) = f.hom x := fun x => by rw [← hgd]; rfl
  have hpt : (χ.comp c).comp (g ≫ e).hom = ι := by
    ext x
    simp only [RingHom.comp_apply, CommRingCat.hom_comp]
    rw [ce, cχ, gd, ← hcomp]; rfl
  obtain ⟨h, hh1, hh2⟩ := habs C' (g ≫ e) (et_comp hg he) (χ.comp c) hpt
  have hed : e ≫ h = d := by
    refine hR A B O Ω ψ g hg hloc (e ≫ h) d ?_ ?_
    · rw [← Category.assoc, hh1, hgd]
    · ext y
      have := DFunLike.congr_fun hh2 (e.hom y)
      simp only [RingHom.comp_apply, CommRingCat.hom_comp] at this ⊢
      rw [this, ce, cχ]
  obtain ⟨s, hs⟩ := hext h hed
  refine ⟨s, hgen Ω _ _ ?_ ?_⟩
  · ext x
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    rw [cχ]; rfl
  · ext y
    have h1 := DFunLike.congr_fun hs y
    have h2 := DFunLike.congr_fun hh2 y
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    rw [h1, h2]

end LateralTheory.E.ColimPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.TwGenNZACPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.TwGenNZACPf

section Field
variable {q : ℕ} [NeZero q] {L : Type} [Field L]

theorem prim_isPrimitiveRoot (z : Prim q L) : IsPrimitiveRoot z.1 q := by
  have : NeZero (q : L) := ⟨z.2.1.ne_zero⟩
  have h := z.2.2
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic] at h
  exact Polynomial.isRoot_cyclotomic_iff.1 h

open Classical in

def lg (q : ℕ) (z x : L) : ZMod q := if h : ∃ n : ℕ, z ^ n = x then (h.choose : ZMod q) else 0

theorem lg_pow {z : L} (hz : IsPrimitiveRoot z q) (n : ℕ) : lg q z (z ^ n) = n := by
  have h : ∃ m : ℕ, z ^ m = z ^ n := ⟨n, rfl⟩
  unfold lg
  rw [dif_pos h, ZMod.natCast_eq_natCast_iff]
  have h2 := h.choose_spec
  have h3 := ((hz.isOfFinOrder (NeZero.ne q)).pow_eq_pow_iff_modEq).1 h2
  rwa [← hz.eq_orderOf] at h3

open Classical in

def fv (q : ℕ) (i : ℤ) (z x : L) : ZMod q :=
  if h : IsUnit (lg q z x) then ((h.unit ^ i : (ZMod q)ˣ) : ZMod q) else 0

theorem fv_rel (i : ℤ) (z : Prim q L) (ζ ξ : Prim q L) (a : (ZMod q)ˣ) (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    fv q i z.1 ξ.1 = ((a ^ i : (ZMod q)ˣ) : ZMod q) * fv q i z.1 ζ.1 := by
  have hz := prim_isPrimitiveRoot z
  obtain ⟨m, -, hm⟩ := hz.eq_pow_of_pow_eq_one (prim_isPrimitiveRoot ζ).pow_eq_one
  have hl : lg q z.1 ξ.1 = lg q z.1 ζ.1 * a := by
    rw [h, ← hm, ← pow_mul, lg_pow hz, lg_pow hz]
    push_cast
    rw [ZMod.natCast_zmod_val]
  unfold fv
  by_cases hu : IsUnit (lg q z.1 ζ.1)
  · have hu' : IsUnit (lg q z.1 ξ.1) := hl ▸ hu.mul a.isUnit
    rw [dif_pos hu, dif_pos hu']
    have : hu'.unit = hu.unit * a := Units.ext (by simp [hl])
    rw [this, mul_zpow, Units.val_mul, mul_comm]
  · have hu' : ¬ IsUnit (lg q z.1 ξ.1) := by
      rw [hl]; exact fun h' => hu ((Units.isUnit_mul_units _ a).1 h')
    rw [dif_neg hu, dif_neg hu', mul_zero]

theorem fv_self (i : ℤ) (z : Prim q L) : fv q i z.1 z.1 = 1 := by
  have hl : lg q z.1 z.1 = 1 := by
    have := lg_pow (prim_isPrimitiveRoot z) 1
    rw [pow_one] at this
    rw [this, Nat.cast_one]
  unfold fv
  have hu : IsUnit (lg q z.1 z.1) := hl ▸ isUnit_one
  rw [dif_pos hu]
  have : hu.unit = 1 := Units.ext (by simp [hl])
  rw [this, one_zpow, Units.val_one]

def lin (i : ℤ) (z : L) : (Prim q L →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination _ (fun ξ : Prim q L => ULift.up (fv q i z ξ.1))

theorem lin_rel (i : ℤ) (z : Prim q L) : twRel q i L ≤ LinearMap.ker (lin i z.1) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, h, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, lin, Finsupp.linearCombination_single]
  rw [sub_eq_zero]
  apply ULift.ext
  simp [fv_rel i z ζ ξ a h]

theorem field_nz (i : ℤ) (z : Prim q L) (c : ZMod q)
    (h : c.val • (Submodule.Quotient.mk (Finsupp.single z 1) : (Prim q L →₀ ULift.{1} (ZMod q)) ⧸ twRel q i L) = 0) :
    c = 0 := by
  have h2 := congrArg ((twRel q i L).liftQ (lin i z.1) (lin_rel i z)) h
  rw [map_nsmul, Submodule.liftQ_apply, map_zero, lin, Finsupp.linearCombination_single, fv_self] at h2
  rw [one_smul] at h2
  have h3 := congrArg AddEquiv.ulift h2
  rw [map_nsmul, map_zero] at h3
  change c.val • (1 : ZMod q) = 0 at h3
  rwa [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val] at h3

end Field

theorem ring_nz {q : ℕ} [NeZero q] (i : ℤ) {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) (c : ZMod q)
    (h : c.val • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) = 0) :
    c = 0 := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  let _ := Ideal.Quotient.field M
  apply field_nz i (ζ.map (Ideal.Quotient.mk M)) c
  have h2 := congrArg (Submodule.mapQ _ _ (Finsupp.lmapDomain (ULift.{1} (ZMod q)) (ULift.{1} (ZMod q))
    (Prim.map (Ideal.Quotient.mk M))) (twRel_le q i (Ideal.Quotient.mk M))) h
  rw [map_nsmul, map_zero, Submodule.mapQ_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single] at h2
  exact h2

theorem gamma_nontrivial (V : Scheme.{0}) [Nonempty V] : Nontrivial Γ(V, ⊤) := by
  obtain ⟨y⟩ := ‹Nonempty V›
  exact RingHom.domain_nontrivial (V.presheaf.germ ⊤ y trivial).hom

theorem TwGenNZAC_of : LateralTheory.E.LCBijPf.TwGenNZAC := by
  intro q _ i K _ _ ζ c h
  let P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) := Scheme.Γ ⋙ twF q i
  let U : Scheme.{0} := Spec (CommRingCat.of K)
  let m : P.obj (op U) := Submodule.Quotient.mk (Finsupp.single (gam ζ) 1)
  have h1 : ((toSheafify Scheme.etaleTopology P).app (op U)).hom (c.val • m) =
      ((toSheafify Scheme.etaleTopology P).app (op U)).hom 0 := by
    rw [map_nsmul, map_zero]
    exact h
  have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) (c.val • m) 0 h1
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  obtain ⟨p⟩ : Nonempty U := inferInstance
  obtain ⟨j, y, -⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 p
  have hj := hle _ _ (Presieve.ofArrows.mk j)
  have : Nonempty (𝒰.X j) := ⟨y⟩
  have : Nontrivial (Scheme.Γ.obj (op (𝒰.X j))) := gamma_nontrivial (𝒰.X j)
  apply ring_nz i ((gam ζ).map (Scheme.Γ.map (𝒰.f j).op).hom) c
  change (P.map (𝒰.f j).op).hom (c.val • m) = (P.map (𝒰.f j).op).hom 0 at hj
  rw [map_nsmul, map_zero] at hj
  change c.val • Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (Scheme.Γ.map (𝒰.f j).op).hom)
    (Finsupp.single (gam ζ) 1)) = _ at hj
  erw [Finsupp.mapDomain_single] at hj
  exact hj

end LateralTheory.E.TwGenNZACPf
end
end

