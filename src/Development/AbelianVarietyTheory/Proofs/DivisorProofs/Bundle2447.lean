import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuativeExistenceOfDvrLiftsLocallyNoetherian
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DvrCriterion

open Scheme.IdealSheafData TopologicalSpace

theorem universallyClosed_of_finite_jointly_surjective {ι : Type} [Finite ι] {X Z : Scheme.{0}}
    (A : ι → Scheme.{0}) (g : ∀ i, A i ⟶ X) (k : X ⟶ Z) (hcov : ∀ x : X, ∃ i, ∃ a, g i a = x)
    (h : ∀ i, UniversallyClosed (g i ≫ k)) : UniversallyClosed k := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have c := fun i ↦ (h i).universally_isClosedMap _ _ _
    ((IsPullback.of_hasPullback i₁ (g i)).paste_horiz H)
  intro Zs hZ
  have e : f' '' Zs = ⋃ i, (pullback.fst i₁ (g i) ≫ f') '' (pullback.fst i₁ (g i) ⁻¹' Zs) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, a, ha⟩ := hcov (i₁ x)
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
      exact Set.mem_iUnion.2 ⟨i, z, by simpa [hz] using hx, by simp [hz]⟩
    · intro y hy
      obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.1 hy
      exact ⟨_, hz, by simp⟩
  rw [e]
  exact isClosed_iUnion_of_finite fun i ↦ c i _ (hZ.preimage (Scheme.Hom.continuous _))

theorem universallyClosed_snd_of_lift {Y S : Scheme.{0}} (π : Y ⟶ S) [LocallyOfFiniteType π]
    [QuasiCompact π] [IsSeparated π] (R : Type) [CommRing R] [IsNoetherianRing R] (u : Sp R ⟶ S)
    (H : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      (x : Sp (FractionRing V) ⟶ Y) (y : Sp V ⟶ S), x ≫ π = Out.jK V ≫ y →
        ∃ x' : Sp V ⟶ Y, Out.jK V ≫ x' = x ∧ x' ≫ π = y) :
    UniversallyClosed (pullback.snd π u) := by
  classical
  set s := pullback.snd π u with hs
  have : CompactSpace (pullback π u : Scheme.{0}) := QuasiCompact.compactSpace_of_compactSpace s
  have : IsLocallyNoetherian (pullback π u : Scheme.{0}) := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsNoetherian (pullback π u : Scheme.{0}) := {}
  let C : irreducibleComponents (pullback π u : Scheme.{0}) → Closeds (pullback π u : Scheme.{0}) :=
    fun c ↦ ⟨c.1, isClosed_of_mem_irreducibleComponents _ c.2⟩
  have : Finite (irreducibleComponents (pullback π u : Scheme.{0})) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  have hr : ∀ c, Set.range (vanishingIdeal (C c)).subschemeι = c.1 := fun c ↦ by
    rw [range_subschemeι, coe_support_vanishingIdeal]; rfl
  refine universallyClosed_of_finite_jointly_surjective (fun c ↦ (vanishingIdeal (C c)).subscheme)
    (fun c ↦ (vanishingIdeal (C c)).subschemeι) s (fun x ↦ ?_) (fun c ↦ ?_)
  · refine ⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
    have : x ∈ Set.range (vanishingIdeal (C ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩)).subschemeι := by
      rw [hr]; exact mem_irreducibleComponent
    exact this
  set I := vanishingIdeal (C c)
  have : IsReduced I.subscheme := GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal _
  have : IrreducibleSpace (Set.range I.subschemeι) := by
    have h1 : IsIrreducible (Set.range I.subschemeι) := by rw [hr]; exact c.2.1
    exact Subtype.irreducibleSpace h1
  have : IrreducibleSpace I.subscheme :=
    I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.irreducibleSpace_iff.2 this
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hP : IsProper (I.subschemeι ≫ s) := by
    refine GlobalTheory.TraitProper.isProper_of_lift_genericPoint R I.subscheme (I.subschemeι ≫ s) ?_
    intro V K _ _ _ _ _ _ _ x y _ hxy
    let e : FractionRing V ≃ₐ[V] K := IsLocalization.algEquiv (nonZeroDivisors V) (FractionRing V) K
    let ε : K →+* FractionRing V := e.symm.toRingEquiv.toRingHom
    let ε' : FractionRing V →+* K := e.toRingEquiv.toRingHom
    have he1 : Spec.map (CommRingCat.ofHom ε) ≫ spMap (algebraMap V K) = Out.jK V := by
      rw [spMap, ← Spec.map_comp]
      congr 2
      ext a
      exact e.symm.commutes a
    have he2 : Spec.map (CommRingCat.ofHom ε') ≫ Out.jK V = spMap (algebraMap V K) := by
      rw [spMap, Out.jK, ← Spec.map_comp]
      congr 2
      ext a
      exact e.commutes a
    have he3 : Spec.map (CommRingCat.ofHom ε') ≫ Spec.map (CommRingCat.ofHom ε) = 𝟙 _ := by
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 2
      ext a
      exact e.apply_symm_apply a
    let xF : Sp (FractionRing V) ⟶ Y :=
      Spec.map (CommRingCat.ofHom ε) ≫ x ≫ I.subschemeι ≫ pullback.fst π u
    have hxF : xF ≫ π = Out.jK V ≫ (y ≫ u) := by
      have : xF ≫ π = Spec.map (CommRingCat.ofHom ε) ≫ (x ≫ I.subschemeι ≫ s) ≫ u := by
        simp [xF, hs, pullback.condition]
      rw [this, hxy, ← he1]
      simp
    obtain ⟨x'', hx1, hx2⟩ := H V xF (y ≫ u) hxF
    let x3 : Sp V ⟶ pullback π u := pullback.lift x'' y hx2
    have h3 : Out.jK V ≫ x3 = Spec.map (CommRingCat.ofHom ε) ≫ x ≫ I.subschemeι := by
      apply pullback.hom_ext
      · simp only [x3, Category.assoc, pullback.lift_fst]
        exact hx1
      · have : Spec.map (CommRingCat.ofHom ε) ≫ (x ≫ I.subschemeι ≫ s) = Out.jK V ≫ y := by
          rw [hxy, ← he1]; simp
        simp only [x3, Category.assoc, pullback.lift_snd]
        exact this.symm
    have hdom : IsDominant (Out.jK V) := by
      have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective _ _
      refine ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_⟩
      exact ((RingHom.injective_iff_ker_eq_bot _).mp hinj).le.trans bot_le
    have hrange : Set.range x3 ⊆ (C c : Set (pullback π u : Scheme.{0})) := by
      rintro _ ⟨v, rfl⟩
      have hv : v ∈ closure (Set.range (Out.jK V)) := (Out.jK V).denseRange v
      have := map_mem_closure x3.continuous hv (t := (C c : Set (pullback π u : Scheme.{0}))) (by
        rintro _ ⟨w, rfl⟩
        change x3 (Out.jK V w) ∈ c.1
        rw [← Scheme.Hom.comp_apply, h3, ← hr c]
        exact ⟨(Spec.map (CommRingCat.ofHom ε) ≫ x) w, by rw [← Scheme.Hom.comp_apply, Category.assoc]⟩)
      rwa [(C c).isClosed.closure_eq] at this
    have hker : I.subschemeι.ker ≤ x3.ker := by
      rw [I.ker_subschemeι]
      exact GlobalTheory.ReducedSubgroup.vanishingIdeal_le_ker x3 (C c) hrange
    refine ⟨IsClosedImmersion.lift I.subschemeι x3 hker, ?_⟩
    rw [← cancel_mono I.subschemeι, Category.assoc, IsClosedImmersion.lift_fac, ← he2,
      Category.assoc, h3, ← Category.assoc, ← Category.assoc, he3, Category.id_comp]
  exact inferInstance

theorem existence_of_lift_discreteValuationRing : ∀ {Y S : Scheme.{0}} [IsLocallyNoetherian S] (π : Y ⟶ S), LocallyOfFiniteType π → QuasiCompact π → IsSeparated π → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (x : Sp (FractionRing V) ⟶ Y) (y : Sp V ⟶ S), x ≫ π = Out.jK V ≫ y → ∃ x' : Sp V ⟶ Y, Out.jK V ≫ x' = x ∧ x' ≫ π = y) → ValuativeCriterion.Existence π := by
  intro Y S _ π _ _ _ H
  have hUC : UniversallyClosed π := by
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @UniversallyClosed) S.affineOpenCover.openCover]
    intro i
    have := S.affineOpenCover.map_prop i
    have hR : IsNoetherianRing (S.affineOpenCover.X i) :=
      isLocallyNoetherian_Spec.1 (isLocallyNoetherian_of_isOpenImmersion (S.affineOpenCover.f i))
    exact @universallyClosed_snd_of_lift Y S π _ _ _ (S.affineOpenCover.X i) _ hR
      (S.affineOpenCover.openCover.f i) H
  have h := hUC
  rw [UniversallyClosed.eq_valuativeCriterion] at h
  exact h.1

end GlobalTheory.DvrCriterion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueWeightSectionFlagSpaceEqRuleAtFramedPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHS.BridgeValue

theorem exists_gen_unit {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]
    (P P' : FrPt Xo c S) (e : P'.x = P.x) : ∃ u : Sˣ, ∀ i, (e ▸ P'.s).f i = scal P.x (u : S) i * P.s.f i := by
  obtain ⟨x', xo', v', t1', t2', t3', s', t4'⟩ := P'
  dsimp only at e
  subst e
  exact gen_unit P.s s' P.gen t4'

end GlobalTheory.CompHS.BridgeValue

namespace GlobalTheory.CompHS.BridgeValue

theorem val_sec₀_eq_evR : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (la : AllWt.Weight Dw) (σ : c.F →+* ℂ) (W : (Y₀ TF.X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ TF.X Z la).ι) (φ : c.F →+* Γ(Y₀ TF.X Z, W)) (x : Sp Γ(Y₀ TF.X Z, W) ⟶ gen TF.Y) (hx : ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ≫ TF.X.π = x ≫ genι TF.Y) (hz : ⊤ ≤ ((show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U (i PUnit.unit)) (fr : GlobalTheory.ShFam.EigFrame TF.Y φ (x ≫ genι TF.Y)), (∀ (τ : E →+* ℂ) (j : Fin (Dw.mult τ)), fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (TF.X.F.vecAt (i PUnit.unit) _ hz hx τ j)).left) → ∀ (ψ : Γ(Y₀ TF.X Z, W) →+* ℂ) (y : FrPt Xo c (CAt σ)), ψ.comp φ = σ → GlobalTheory.ShFam.BdArc.Matches fr ψ y → ∀ (g : AllWt.secZ Xo c (AllWt.exOf Dw la 0)) (hO : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ U₀ TF.X Z) (hi : ⊤ ≤ (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ TF.X Z la).U i), H0.val (spMap ψ ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) i hO hi (sec₀ TF.X Z _ g) = toC (evR Xo c g.1 y) := by
  intro E _ _ _ H Dw l Xo c TF Z la σ W hW i φ x hx hz fr hfr ψ y hψ hm g hO hi
  let k := i PUnit.unit
  let ψ' : Γ(Y₀ TF.X Z, W) →+* CAt σ := ψ
  let q : Sp Γ(Y₀ TF.X Z, W) ⟶ TF.X.YY := (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec) ≫ inc₀ TF.X Z
  let z' : Sp (CAt σ) ⟶ TF.X.YY := spMap ψ' ≫ q
  have hz' : ⊤ ≤ z' ⁻¹ᵁ TF.X.F.U k := GlobalTheory.FlagMod.le_preimage_comp _ hz
  have hO' : ⊤ ≤ z' ⁻¹ᵁ flagOpen TF.X := fun s hs => hO hs
  have hpt : AllWt.ptF y = GlobalTheory.FlagMod.frX y := rfl
  have ex : spMap ψ' ≫ (x ≫ genι TF.Y) = z' ≫ TF.X.π := by
    rw [← hx]; exact (Category.assoc _ _ _).symm
  have hxy : GlobalTheory.FlagMod.frX y ≫ TF.Y.j = z' ≫ TF.X.π := by
    calc GlobalTheory.FlagMod.frX y ≫ TF.Y.j = (AllWt.ptF y ≫ TF.Y.jQ) ≫ genι TF.Y := by rw [Category.assoc]; rfl
    _ = spMap ψ' ≫ (x ≫ genι TF.Y) := by rw [hm.1, Category.assoc]
    _ = z' ≫ TF.X.π := ex
  obtain ⟨Q, hQ⟩ := TF.X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd y) hxy.symm k hz'
  have hv : ∀ τ j, GlobalTheory.FlagMod.frVec TF.Y y hxy τ j = GlobalTheory.FlagMod.frVec TF.Y Q hQ.over τ j := fun τ j => by
    rw [hQ.frVec_eq rfl hQ.over τ]
    refine (GlobalTheory.FlagMod.toModel_eq_iff _ _ _ _ _).2 ?_
    obtain ⟨w, h1, h2, h3⟩ := hm.2 τ j
    refine ⟨w, h1, h2, h3.trans ?_⟩
    rw [hfr τ j, ← TF.X.F.tanPull_vecAt k ψ' q hz hz' hx rfl ex]
    rfl
  have eQ : y.x = Q.x := by
    rw [← GlobalTheory.FlagMod.frX_fst, ← GlobalTheory.FlagMod.frX_fst,
      GlobalTheory.FlagMod.xF_ext (Y := TF.Y) (GlobalTheory.FlagMod.frX_snd y) (GlobalTheory.FlagMod.frX_snd Q) (hxy.trans hQ.over.symm)]
  obtain ⟨u0, hu0⟩ := exists_gen_unit Q y eQ
  let t : Ix Dw → (CAt σ)ˣ := fun ix => ix.elim u0 fun _ => 1
  have ht : FrBor t Q y := GlobalTheory.FlagMod.frBor_of_frVec (TF.X.F.inM hz' rfl) hQ.over hxy t (fun _ => 1)
    (fun _ => Matrix.blockTriangular_one) (fun _ i => Matrix.one_apply_eq i)
    (fun τ j => by
      rw [hv τ j]
      refine ((Fintype.sum_eq_single j fun j' hj' => ?_).trans ?_).symm
      · show (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) j' j • _ = 0
        rw [Matrix.one_apply_ne hj', zero_smul]
      · show (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) j j • _ = _
        rw [Matrix.one_apply_eq, one_smul]) (fun _ => hu0)
  have he := evR_eq_val_secOf (X := TF.X) g hO' hQ ht
  have hprod : (∏ ix, t ix ^ AllWt.exOf Dw la 0 ix) = 1 := by
    rw [Fintype.prod_option, GlobalTheory.FlagMod.exOf_none, zpow_zero, _root_.one_mul]
    exact Finset.prod_eq_one fun _ _ => one_zpow _
  rw [hprod, Units.val_one, _root_.one_mul] at he
  have key : ∀ (a b : Sp (CAt σ) ⟶ TF.X.YY), a = b → ∀ hOa hia hOb hib,
      H0.val (B := TF.X.LL (AllWt.exOf Dw la 0)) a k hOa hia (secOf TF.X _ g) =
        H0.val (B := TF.X.LL (AllWt.exOf Dw la 0)) b k hOb hib (secOf TF.X _ g) := by
    intro a b hab; subst hab; intros; rfl
  refine (H0.val_pull (inc₀ TF.X Z) le_rfl _ i hO hi (fun s hs => hO' hs) (fun s hs => hz' hs) _).trans ?_
  refine (key _ _ (Category.assoc _ _ _) _ _ hO' hz').trans ?_
  exact he.symm

end GlobalTheory.CompHS.BridgeValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightAntitoneBoundary
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftGaps

theorem antitone_of_step {N : ℕ} {f : Fin N → ℤ} (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b ≤ f a) : Antitone f := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  simp only [Fin.mk_le_mk] at hab
  induction b with
  | zero =>
    obtain rfl : a = 0 := by omega
    exact le_rfl
  | succ n ih =>
    rcases Nat.lt_or_ge a (n + 1) with h' | h'
    · exact (h ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl).trans (ih (by omega) (by omega))
    · obtain rfl : a = n + 1 := by omega
      exact le_rfl

theorem isQuot_u₁ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (P : WtPar Dw) (kc : ℕ) (hk : P.a + 1 = kc) : IsQuot Dw kc P.T P.c₀ P.u P.u₁ := by
  intro τ
  refine ⟨fun a (ha : (a : ℕ) + 1 = kc) => (P.anchored τ (by omega)).1, fun a b hb => ?_⟩
  have hb' : (a : ℕ) + 1 < Dw.p + Dw.q := hb ▸ b.2
  show P.u₁ τ a - P.u₁ τ b = (P.u τ a - P.u τ b + if (b : ℕ) = Dw.p then -P.c₀ - (2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2) else 2) /
    ((P.T : ℤ) + CompHt.dimFlag Dw + 1)
  rw [← CompHS.gap_eq (P.u₁ τ) hb, P.gap_u₁ τ hb', P.gap_uMinus_sub_kap τ hb', CompHS.gap_eq (P.u τ) hb, hb,
    WtPar.T₁, dimFlag_eq]

section Pt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem nCol_le (PP A M : ℝ) (hw : WtNum p i PP) (hh : HostNum D L PP A M) :
    GlobalTheory.RefSum.nCol (dat p i) ≤ 2 * D.R.r * (D.R.f * D.R.r) + 8 * (D.R.f * D.R.r) + 8 := by
  obtain ⟨-, -, s3⟩ := hw.sig
  have hcard : Fintype.card (Lt1 (dat p i)) = D.R.f * D.R.r := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [GlobalTheory.RefSum.sum_mult, hh.deg, s3]
    simp
  have hmult : ∀ τ, (dat p i).mult τ ≤ D.R.r := fun τ => by
    rw [← s3]; unfold Datum.mult; split_ifs <;> omega
  have hsum : ∑ f : Lt1 (dat p i), 2 * GlobalTheory.FactorDepth.rk f ≤ Fintype.card (Lt1 (dat p i)) * (2 * D.R.r) := by
    rw [← smul_eq_mul, ← Finset.card_univ]
    refine Finset.sum_le_card_nsmul _ _ _ fun f _ => ?_
    have := GlobalTheory.FactorDepth.rk_le f
    have := hmult f.1
    omega
  rw [hcard] at hsum
  unfold GlobalTheory.RefSum.nCol
  have h8 : 8 * ((∑ f : Lt1 (dat p i), 2 * GlobalTheory.FactorDepth.rk f) / 8) ≤ ∑ f : Lt1 (dat p i), 2 * GlobalTheory.FactorDepth.rk f :=
    Nat.mul_div_le _ _
  rw [hcard]
  have : D.R.f * D.R.r * (2 * D.R.r) = 2 * D.R.r * (D.R.f * D.R.r) := by ring
  omega

theorem cols_le_len (PP A M : ℝ) (hw : WtNum p i PP) (hh : HostNum D L PP A M) :
    (GlobalTheory.RefSum.nCol (dat p i) + 1) * (CompHt.dimFlag (dat p i) + 3) ≤ lenT p i PP := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hr6 : 6 ≤ D.R.r := by omega
  have hf8 := hh.f8
  have hn := nCol_le p i PP A M hw hh
  have hZ : (40 : ℝ) ≤ zBase L := by
    unfold zBase
    have a1 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf8
    have a2 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr6
    have a3 : (48 : ℝ) ≤ D.R.f * D.R.r := by nlinarith
    have a4 : (10 : ℝ) ≤ L.sc.L := hh.big.2.1
    nlinarith
  have hPP : (40 : ℝ) ≤ PP := hZ.trans ((le_self_pow₀ (by linarith) (by norm_num)).trans hh.ppLow)
  have hD : ((CompHt.dimFlag (dat p i) : ℕ) : ℝ) = (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) := by
    rw [hw.dim]; push_cast [Nat.cast_choose_two]; ring
  set Dd : ℝ := ((CompHt.dimFlag (dat p i) : ℕ) : ℝ) with hDd
  have F8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf8
  have R6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr6
  have FR : (48 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
  have hDd1 : (1 : ℝ) ≤ Dd := by rw [hD]; nlinarith
  have hn' : (GlobalTheory.RefSum.nCol (dat p i) : ℝ) + 1 ≤ 17 * Dd := by
    have : (GlobalTheory.RefSum.nCol (dat p i) : ℝ) ≤ 2 * D.R.r * (D.R.f * D.R.r) + 8 * (D.R.f * D.R.r) + 8 := by
      exact_mod_cast hn
    rw [hD]
    have h13 : (45 : ℝ) ≤ 13 * D.R.r - 33 := by linarith
    have : (48 : ℝ) * 45 ≤ ((D.R.f : ℝ) * D.R.r) * (13 * D.R.r - 33) := mul_le_mul FR h13 (by norm_num) (by linarith)
    nlinarith
  have hm0 : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have hkm : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hT : 1600 * Dd ^ 2 ≤ (lenT p i PP : ℝ) := by
    have h1 : 1600 * Dd ^ 2 ≤ PP ^ 2 * Dd ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
      rw [le_div_iff₀ hm0]
      have c5 : (1600 : ℝ) ≤ PP ^ 2 := by nlinarith
      have c6 : (0 : ℝ) ≤ Dd ^ 2 := by positivity
      calc 1600 * Dd ^ 2 * D.R.m ≤ PP ^ 2 * Dd ^ 2 * D.R.m :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right c5 c6) hm0.le
        _ ≤ PP ^ 2 * Dd ^ 2 * D.R.k := mul_le_mul_of_nonneg_left hkm (by positivity)
    exact h1.trans (Nat.le_ceil _)
  have hmain : ((GlobalTheory.RefSum.nCol (dat p i) : ℝ) + 1) * (Dd + 3) ≤ (lenT p i PP : ℝ) := by
    have e1 : Dd + 3 ≤ 4 * Dd := by linarith
    have : ((GlobalTheory.RefSum.nCol (dat p i) : ℝ) + 1) * (Dd + 3) ≤ (17 * Dd) * (4 * Dd) :=
      mul_le_mul hn' e1 (by linarith) (by linarith)
    nlinarith
  rw [hDd] at hmain
  exact_mod_cast hmain

theorem gapsAt (PP A M : ℝ) (hi : (i : ℕ) + 1 < D.R.m) (hw : WtNum p i PP) (hh : HostNum D L PP A M) :
    1 ≤ (dat p i).p ∧ ∀ la ∈ ({(⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁,
      (⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))),
      (∀ τ, Antitone (la τ)) ∧ ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = (dat p i).p →
        (b : ℕ) = (dat p i).p → (GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1 ≤ la τ a - la τ b := by
  obtain ⟨s1, s2, s3⟩ := hw.sig
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have ep : (dat p i).p = D.R.k + i := by rw [s1]; unfold Ranks.sigW; omega
  have eq : (dat p i).q = D.R.m - ((i : ℕ) + 1) := by rw [s2]; rfl
  have hcl := cols_le_len p i PP A M hw hh
  set P : WtPar (dat p i) := ⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ with hP
  have hPa : P.a + 1 = D.R.k - 1 := by show D.R.k - 2 + 1 = D.R.k - 1; omega
  have hquo : Quo p i PP P.u₁ := isQuot_u₁ (dat p i) P (D.R.k - 1) hPa
  obtain ⟨h0, S, eta, -, -, -, hT2, -, hH⟩ := hw.hyp hi
  have hW := hH P.u₁
  have hdiv := (quo_iff p i PP h0 S eta P.u₁).1 hquo
  have G := GlobalTheory.MeanTop.divided_gaps _ _ _ hW hdiv
  have hT1 := hW.h1
  simp only [wtsAt] at G hT1

  have gin : ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → 0 ≤ P.u₁ τ a - P.u₁ τ b := by
    intro τ a b hb
    obtain ⟨g1, g2, -⟩ := G τ a b hb
    by_cases hbp : (b : ℕ) = (dat p i).p
    · have g := (g2 hbp).1
      have hT0 : (0 : ℤ) < 2 * (lenT p i PP : ℤ) := by omega
      by_contra hc
      push_neg at hc
      have := mul_neg_of_pos_of_neg hT0 hc
      nlinarith
    · have g := g1 hbp
      have : (0 : ℤ) ≤ (lenT p i PP : ℤ) + CompHt.dimFlag (dat p i) + 2 + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by
        positivity
      omega
  have gbar : ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → (b : ℕ) = (dat p i).p →
      (lenT p i PP : ℤ) ≤ P.u₁ τ a - P.u₁ τ b := by
    intro τ a b hb hbp
    obtain ⟨-, g2, -⟩ := G τ a b hb
    have g := (g2 hbp).2
    have hT0 : (0 : ℤ) < 4 * (lenT p i PP : ℤ) := by omega
    have hle : (lenT p i PP : ℤ) ≤ P.u₁ τ a - P.u₁ τ b - 3 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by
      by_contra hc
      push_neg at hc
      have := mul_lt_mul_of_pos_left hc hT0
      nlinarith
    have : (0 : ℤ) ≤ (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by positivity
    linarith

  have gub : ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 →
      P.ub τ a - P.ub τ b = (P.u₁ τ a - P.u₁ τ b) / ((dimFlag (dat p i) : ℤ) + 3) := by
    intro τ a b hb
    have hb' : (a : ℕ) + 1 < (dat p i).p + (dat p i).q := hb ▸ b.2
    rw [← CompHS.gap_eq (P.ub τ) hb, P.gap_ub τ hb', CompHS.gap_eq (P.u₁ τ) hb]
  have hcl' : ((GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1) * ((dimFlag (dat p i) : ℤ) + 3) ≤ (lenT p i PP : ℤ) := by
    rw [← dimFlag_eq]; exact_mod_cast hcl
  have hD0 : (0 : ℤ) < (dimFlag (dat p i) : ℤ) + 3 := by positivity
  have hD1 : (1 : ℤ) ≤ (dimFlag (dat p i) : ℤ) + 3 := by omega
  have hnT : (GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1 ≤ (lenT p i PP : ℤ) := by
    have : (0 : ℤ) ≤ (GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1 := by positivity
    nlinarith
  refine ⟨by omega, fun la hla => ?_⟩
  rcases hla with rfl | hla
  · refine ⟨fun τ => antitone_of_step fun a b hb => by have := gin τ a b hb; omega, fun τ a b ha hb => ?_⟩
    exact hnT.trans (gbar τ a b (by omega) hb)
  · rw [Set.mem_singleton_iff] at hla
    subst hla
    refine ⟨fun τ => antitone_of_step fun a b hb => ?_, fun τ a b ha hb => ?_⟩
    · have e := gub τ a b hb
      have := Int.ediv_nonneg (gin τ a b hb) hD0.le
      omega
    · rw [gub τ a b (by omega)]
      exact Int.le_ediv_of_mul_le hD0 (hcl'.trans (gbar τ a b (by omega) hb))

end Pt

theorem lift_gaps : Size → Covers fun Fm x _ ι p i Y PP _ => 1 ≤ (dat p i).p ∧ ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), (∀ τ, Antitone (la τ)) ∧ ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = (dat p i).p → (b : ℕ) = (dat p i).p → (GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1 ≤ la τ a - la τ b := by
  intro _
  have hw : WtN := WtShape.wtN
  have hh : HostN 1 := Sizes.hostN 1
  unfold WtN Lifts at hw
  unfold HostN Lifts at hh
  unfold Covers Lifts
  refine Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and hw hh) ?_
  intro eps Fm CH _ h
  obtain ⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩ := h
  refine ⟨0, le_rfl, max x1 x2, fun x hx hle ι p hp i hi Y _ => ?_⟩
  exact gapsAt p i _ _ _ hi (h1 x hx ((le_max_left _ _).trans hle) ι p hp i)
    (h2 x hx ((le_max_right _ _).trans hle) ι p hp i)

end GlobalTheory.LiftGaps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaAwayPowSelf
section
noncomputable section

namespace GlobalTheory.HTSympCover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

def SympCond {b : Base D R} {N : ℕ} {S : Scheme.{0}} {t : S ⟶ Sp R} (o : Obj b N t) (h M : ℕ) (T : Over S)
    (t₁ : T.left ⟶ Sp (cycAway M)) (lv : (Fin h ⊕ Fin h → ℤ) → (T ⟶ o.A)) : Prop :=
  (∀ a c, lv (a + c) = lv a * lv c) ∧ (∀ a, lv a ^ M = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left) (β : cycAway M →+* k) (z : kˣ),
      x ≫ t₁ = spMap β → (z : k) = β (zetaAway M) →
      (∀ a, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a = 1 ↔ ∃ c, a = M • c) ∧
      (∀ g : Over.mk (x ≫ T.hom) ⟶ o.A, g ^ M = 1 →
        ∃ a, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a = g) ∧
      ∀ a c, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) M
        ((Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a)
        ((Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv c) (unitOn (z ^ (2 * omegaStd a c)))

theorem zetaAway_pow_self (M : ℕ) (hM : M ≠ 0) : zetaAway M ^ M = 1 :=
  Subtype.ext (by simpa [zetaAway, zeta] using (Complex.isPrimitiveRoot_exp M hM).pow_eq_one)

theorem zetaAway_pow_eq (M : ℕ) (hM : M ≠ 0) {k k' : ℕ} (h : (k : ZMod M) = k') :
    zetaAway M ^ k = zetaAway M ^ k' := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [← Nat.div_add_mod k M, ← Nat.div_add_mod k' M, pow_add, pow_add, pow_mul, pow_mul, zetaAway_pow_self M hM,
    one_pow, one_pow, h]

theorem isMultOf_unique {h M : ℕ} (hh : 1 ≤ h) {a : sympSimGrp h M} {n n' : ℕ} (hn : IsMultOf a n)
    (hn' : IsMultOf a n') : (n : ZMod M) = n' := by
  let i : Fin h := ⟨0, hh⟩
  have e1 := hn (Pi.single (.inl i) 1) (Pi.single (.inr i) 1)
  have e2 := hn' (Pi.single (.inl i) 1) (Pi.single (.inr i) 1)
  have h1 : omegaMod M (Pi.single (Sum.inl i) (1 : ZMod M)) (Pi.single (Sum.inr i) 1) = 1 := by
    simp [omegaMod, Pi.single_apply]
  rw [h1, _root_.mul_one] at e1 e2
  rw [← e1, ← e2]

end GlobalTheory.HTSympCover
end
end

