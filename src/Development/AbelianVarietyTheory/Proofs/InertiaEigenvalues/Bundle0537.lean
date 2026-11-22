import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0508
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0509
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0475
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0518
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0252
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0510
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0478
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0423
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0263
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0302
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0287
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0242
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0253
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0300
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0501
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0388
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOrientedPrismUniformizerFrameBreuilKisinHomStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f : Hom bk.prism B), IsFrame bk B (BK.hf f bk.E) (BK.hf f X) := by
  first | exact @GlobalTheory.BSP.isFrame_hf | exact GlobalTheory.BSP.isFrame_hf | (intros; apply GlobalTheory.BSP.isFrame_hf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotentiallyCrystallineLatticeCoefficientExtensStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPotentiallyCrystalline_latticeCoefficientExtension : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b), (pc Pl h hN hF hS).IsPotCrys T.ρ → (pc Pl h hN hF hS).IsPotCrys (extLat hL T b hb).ρ := by
  first | exact @GlobalTheory.BaseCoef.isPotCrys_extLat | exact GlobalTheory.BaseCoef.isPotCrys_extLat | (intros; apply GlobalTheory.BaseCoef.isPotCrys_extLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStablePrismHomOfFiniteProductComponentsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStablePrismHom_of_finite_product_components : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (n : ℕ) (C : Fin n → Obj l R), (∀ i, ∃ t, (C i).I = Ideal.span {t}) → ∀ (Q : Obj l R) (π : ∀ i, Hom Q (C i)), Function.Bijective (fun (x : Q.A) (i : Fin n) => (π i).f x) → ∀ (B : Obj l R) (h : Hom B Q), (∀ i, Stable ((π i).comp h)) → Stable h := by
  first | exact @GlobalTheory.ProdStable.prodStable | exact GlobalTheory.ProdStable.prodStable | (intros; apply GlobalTheory.ProdStable.prodStable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTopRingLL
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem isTopRingLL : IsTopologicalRing (Br.LL D.nbr i w hw) :=
  (goodO_ringOfIntegers (D.nd.l i) (D.nbr i w hw).LL).2.2.2.1

theorem vecL_sub {a : ℕ} (u v : Fin a → Fin D.R.nV → KK D.nd i) :
    vecL i w hw (u - v) = vecL i w hw u - vecL i w hw v := by
  funext b j
  simp [vecL]

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i))

theorem sumG_crys (hr : GoodR D.nd i r) (hAdm : FontaineAtPlacesOverL (D := D)) {a : ℕ} (x : Fin a → ↥Xs)
    (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1)
    (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (hpot : ∀ y : ↥Xs, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys
      (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r y)))) :
    IsCrys ((D.loc (D.nd.l i)).PD K')
      ((sumG i w hw r Xs hr x).ρ.comp (Subgroup.inclusion (GK_le h))) := by
  haveI := isTopRingLL i w hw
  have hc' : ∀ (y : ↥Xs) (v : Fin D.R.nV → Br.LL D.nbr i w hw),
      Continuous fun g => ((Br.loc D.nbr i w hw (rTwO D.nd i r y)).comp (Subgroup.inclusion (GK_le h)) g).mulVec v :=
    fun y v => (contTw i w hw r Xs hr y v).comp (continuous_inclusion (GK_le h))
  have hF' := hAdm (D.nd.l i) K' (D.nbr i w hw).LL
  have hcr : ∀ y : ↥Xs, IsCrys ((D.loc (D.nd.l i)).PD K')
      (matRep ((Br.loc D.nbr i w hw (rTwO D.nd i r y)).comp (Subgroup.inclusion (GK_le h)))) := fun y =>
    (GlobalTheory.T.potentiallyCrystalline_module_eq_crystalline_restriction (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS _
      (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r y)))).2.1 (hpot y)
  exact (cj_sum (Qp := ℚ_[D.nd.l i]) (O := ↥(OL (D.nbr i w hw).LL))
    (fun y : ↥Xs => (Br.loc D.nbr i w hw (rTwO D.nd i r y)).comp (Subgroup.inclusion (GK_le h))) hc' hF'
    (S := fun _ => Set.univ) (fun y => ⟨hcr y, fun τ b _ => Set.mem_univ _⟩) a x).1

theorem yfun_val {a : ℕ} (hr : GoodR D.nd i r) (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (E : Fin a → Fin D.R.nV → KK D.nd i) (hE : ∀ γ : GE D.nd, actK i r Xs x γ E - E ∈ Y)
    (g : Br.G D.nbr i w hw) :
    (spanL i w hw Y).subtype (yfun i w hw r Xs x Y E hE g) =
      (sumG i w hw r Xs hr x).ρ g (vecL i w hw E) - (show (sumG i w hw r Xs hr x).V from vecL i w hw E) := by
  rw [sumG_vecL]
  exact vecL_sub i w hw _ _

end GlobalTheory.Pass.LocDual.OneX

end

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem GlobalTheory.Pass.LocDual.OneX.yfun_Z1fT : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r)
    (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n → ∀ {a : ℕ} (x : Fin a → ↥Xs) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) (E : Fin a → Fin D.R.nV → KK D.nd i)
    (hE : ∀ γ : GE D.nd, actK i r Xs x γ E - E ∈ Y)
    (LY : Lattice (O := Br.OLL D.nbr i w hw) (XG i w hw r Xs hr x Y hst).ρ), LY.T = latY i w hw Y →
    (yfun i w hw r Xs x Y E hE : Br.G D.nbr i w hw → (XG i w hw r Xs hr x Y hst).V) ∈
    latticeFiniteCocycles (Br.PD D.loc D.nbr i w hw) LY := by
  intro D hAdm i r hr Xs w hw n hpf a x Y hst E hE LY hLY
  obtain ⟨K', h, hN, hF, hS, Sig, Fr, -, -, -, -, hall⟩ := hpf
  haveI := isTopRingLL i w hw
  have hF' := hAdm (D.nd.l i) K' (D.nbr i w hw).LL
  have hz : (yfun i w hw r Xs x Y E hE : Br.G D.nbr i w hw → (XG i w hw r Xs hr x Y hst).V) ∈
      finiteCocycles (Br.PD D.loc D.nbr i w hw) (XG i w hw r Xs hr x Y hst).ρ :=
    GlobalTheory.Pass.FinDesc.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF
      (fun A₀ A₁ A₂ ι π h1 h2 h3 h4 h5 hA =>
        ⟨((hF'.1 A₀ A₁ A₂ ι π h1 h2 h3 h4 h5).1 hA).1, ((hF'.1 A₀ A₁ A₂ ι π h1 h2 h3 h4 h5).1 hA).2.1⟩)
      (sumG i w hw r Xs hr x) (XG i w hw r Xs hr x Y hst) (spanL i w hw Y).subtype
      (spanL i w hw Y).injective_subtype (fun g v => rfl)
      (sumG_crys i w hw r Xs hr hAdm x K' h hN hF hS (fun y => (hall y).1)) (vecL i w hw E)
      (yfun i w hw r Xs x Y E hE) (yfun_val i w hw r Xs hr x Y E hE)
  refine ⟨⟨hz.1, fun g _ => ?_⟩, hz⟩
  have hm : (yfun i w hw r Xs x Y E hE g : ↥(spanL i w hw Y)) ∈ latY i w hw Y :=
    Submodule.subset_span ⟨_, hE _, rfl⟩
  show yfun i w hw r Xs x Y E hE g ∈ LY.T
  rw [hLY]
  exact hm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomBaseChangeOntoStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeHomBaseChange_onto : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (k₁ k₂ : ℕ) (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L), F.Onto → (extHom hL hb₁ hb₂ F).Onto := by
  first | exact @GlobalTheory.BaseCoef.extHom_onto | exact GlobalTheory.BaseCoef.extHom_onto | (intros; apply GlobalTheory.BaseCoef.extHom_onto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenModMonoLeftStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lenMod_mono_left' : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (S S' H : Submodule O M), S ≤ S' → BlochKatoDuality.lenMod S H ≤ BlochKatoDuality.lenMod S' H := by
  first | exact @GlobalTheory.lenMod_mono_left | exact GlobalTheory.lenMod_mono_left | (intros; apply GlobalTheory.lenMod_mono_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenModSpanSUnionLeOfDirected
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.Pass.LocDirect

theorem lenMod_span_sUnion_le_of_directed : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S : Set (Set M)) (H : Submodule O M) (N : ℕ∞),
    (∀ A ∈ S, ∀ B ∈ S, ∃ C ∈ S, A ⊆ C ∧ B ⊆ C) →
    (∀ A ∈ S, BlochKatoDuality.lenMod (Submodule.span O A) H ≤ N) →
    BlochKatoDuality.lenMod (Submodule.span O (⋃₀ S)) H ≤ N := by
  intro O M _ _ _ S H N hdir hA
  classical
  apply GlobalTheory.Pass.LocDual.lenMod_span_le_of_finset
  intro F hF
  rcases S.eq_empty_or_nonempty with hS | ⟨A0, hA0⟩
  · have hF0 : (↑F : Set M) = ∅ := by
      rw [hS, Set.sUnion_empty] at hF
      exact Set.subset_empty_iff.mp hF
    rw [hF0, Submodule.span_empty, GlobalTheory.Pass.LocDual.lenMod_eq_height_map, Submodule.map_bot,
      Order.height_bot]
    exact zero_le
  · have key : ∀ G : Finset M, (↑G : Set M) ⊆ ⋃₀ S → ∃ A ∈ S, (↑G : Set M) ⊆ A := by
      intro G
      induction G using Finset.induction_on with
      | empty => intro _; exact ⟨A0, hA0, by simp⟩
      | insert a G ha ih =>
        intro hG
        rw [Finset.coe_insert, Set.insert_subset_iff] at hG
        obtain ⟨B, hB, haB⟩ := hG.1
        obtain ⟨A, hA', hGA⟩ := ih hG.2
        obtain ⟨C, hC, hAC, hBC⟩ := hdir A hA' B hB
        refine ⟨C, hC, ?_⟩
        rw [Finset.coe_insert, Set.insert_subset_iff]
        exact ⟨hBC haB, hGA.trans hAC⟩
    obtain ⟨A, hAS, hFA⟩ := key F hF
    refine le_trans ?_ (hA A hAS)
    rw [GlobalTheory.Pass.LocDual.lenMod_eq_height_map, GlobalTheory.Pass.LocDual.lenMod_eq_height_map]
    exact Order.height_mono (Submodule.map_mono (Submodule.span_mono hFA))

end GlobalTheory.Pass.LocDirect
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthModuloSpanLeOfForallFinsetStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lengthModulo_span_le_of_forall_finset : ∀ {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (S : Set M) (H : Submodule O M) (b : ℕ∞),
    (∀ F : Finset M, (↑F : Set M) ⊆ S → BlochKatoDuality.lenMod (Submodule.span O (↑F : Set M)) H ≤ b) →
    BlochKatoDuality.lenMod (Submodule.span O S) H ≤ b := by
  first | exact @GlobalTheory.Pass.LocDual.lenMod_span_le_of_finset | exact GlobalTheory.Pass.LocDual.lenMod_span_le_of_finset | (intros; apply GlobalTheory.Pass.LocDual.lenMod_span_le_of_finset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthQuotEqZeroIff
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.CutCore

theorem length_mono {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] {A B : Submodule O M} (h : A ≤ B) :
    Module.length O ↥A ≤ Module.length O ↥B :=
  Module.length_le_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

theorem exists_length_quot {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {a : O} (ha : a ≠ 0) :
    ∃ n : ℕ, Module.length O (O ⧸ Ideal.span {a}) = n := by
  have h : Ring.ord O a ≠ ⊤ := by
    rwa [Ring.ord_eq_addVal, Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  obtain ⟨e, he⟩ := ENat.ne_top_iff_exists.mp h
  exact ⟨e, he.symm⟩

theorem length_quot_eq_zero_iff {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {a : O} :
    Module.length O (O ⧸ Ideal.span {a}) = 0 ↔ IsUnit a := by
  change Ring.ord O a = 0 ↔ _
  rw [Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_eq_zero_iff]

variable {D : D7} (i : D.nd.Loc)

theorem resIne_eq_bot_of_le {k : ℕ} {A B : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)} (h : A ≤ B)
    {v : HeightOneSpectrum (𝓞 D.host.E)} (hB : resIne i B v = ⊥) : resIne i A v = ⊥ :=
  le_bot_iff.mp (hB ▸ Submodule.map_mono h)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem lenCob_mono {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    {A B : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)} (h : A ≤ B) : lenCob i M A ≤ lenCob i M B :=
  length_mono (inf_le_inf_right _ h)

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i))
  (S : IdempotentChoiceData D.nd i)

theorem inR'_one : InR' D.nd r S 1 :=
  ⟨1, fun _ => 1, fun _ => 1, fun _ => S.T'.one_mem, by
    funext x'
    simp⟩

theorem del_ne_zero (hS : GoodCongruenceObjects D.nd r ρ π S) : del51 D.nd S S.π' ≠ 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨h1, -, h3, -⟩, -⟩ := hS
  intro h0
  have hz : (Eel D.nd S S.π').map (toK D.nd i) = 0 := by
    rw [← Matrix.toLin'.map_eq_zero_iff]
    refine LinearMap.ext fun u => ?_
    apply S.e.injective
    rw [Matrix.toLin'_apply, h3 u, h0]
    simp [Prod.ext_iff, funext_iff]
  have := h1 S.π'
  rw [hz, Matrix.rank_zero] at this
  exact zero_ne_one this

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem length_cocRho_le (eρ : ℕ) (hr : GoodR D.nd i r) (hS : GoodCongruenceObjects D.nd r ρ π S) (hπ : π ∈ Xs)
    (hU : UnrOut i r Xs)
    (hL : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), LocBound i w hw r Xs (WpO D.nd i ρ π) eρ) :
    Module.length (D.nd.O i) ↥(cocRho i r S Xs) ≤
      (((placesOver D.host.E (D.nd.l i)).ncard * eρ : ℕ) : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i) +
        (((2 * D.R.r : ℕ) : ℕ∞) * lenQ i (del51 D.nd S S.π') +
          Module.length (D.nd.O i) ↥(Br.selPi D.loc D.nbr i ρ π)) := by
  obtain ⟨C, hC, hfin, hlen⟩ := GlobalTheory.T.length_global_cocycles_le_sum_places_over D i r Xs _ (WpO D.nd i ρ π) (cocRho i r S Xs) eρ
    (fun w hw => ⟨hL w hw, (GlobalTheory.T.localised_global_cocycles_in_local_span D i r ρ π Xs S hr hS hπ w hw).1⟩)
  refine hlen.trans (add_le_add le_rfl ?_)
  refine (GlobalTheory.T.length_cocycles_le_coboundaries_add_selmer D i ρ π C (hC.trans (GlobalTheory.T.finiteQuotientCocycleSpan_rho_char_le_cocycles D i r ρ π Xs S hr hS hπ).1) hfin ?_).trans
    (add_le_add ((lenCob_mono i _ hC).trans (GlobalTheory.T.length_coboundaries_among_block_cocycles_le D i r ρ π Xs S hr hS hπ).1) le_rfl)
  intro v h1 h2 h3
  exact resIne_eq_bot_of_le i hC
    (GlobalTheory.Proof.LocalGlobalSelmer.main D i r Xs S _ S.ψρ (inR'_one i r S) hU v h1 h2 h3)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem exists_fin_unr (eχ : ℕ) (hr : GoodR D.nd i r) (hS : GoodCongruenceObjects D.nd r ρ π S) (hπ : π ∈ Xs)
    (hU : UnrOut i r Xs)
    (hSv : ∀ v ∈ D.nd.S i, (QuadAt i r Xs v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Xs π v)
    (hQ : ∀ v ∈ D.nd.Q i, QuadAt i r Xs v) (c : Fin D.R.t)
    (hL : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      LocBound i w hw r Xs (chiRatO D.nd i ((c : ℕ) + 1)) eχ) :
    ∃ C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) 1), C ≤ cocChi i r S Xs c ∧
      (∀ f ∈ C, IsFinL i (chiRatO D.nd i ((c : ℕ) + 1)) f) ∧
      (∀ v, v ∉ placesOver D.host.E (D.nd.l i) → resIne i C v = ⊥) ∧
      Module.length (D.nd.O i) ↥(cocChi i r S Xs c) ≤
        (((placesOver D.host.E (D.nd.l i)).ncard * eχ : ℕ) : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i) +
          (Module.length (D.nd.O i) ↥C + ∑ q ∈ D.nd.Q i, lenQ i (D.nd.zeta i q - 1)) := by
  obtain ⟨C, hC, hfin, hlen⟩ := GlobalTheory.T.length_global_cocycles_le_sum_places_over D i r Xs _ (chiRatO D.nd i ((c : ℕ) + 1)) (cocChi i r S Xs c) eχ
    (fun w hw => ⟨hL w hw, (GlobalTheory.T.localised_global_cocycles_in_local_span D i r ρ π Xs S hr hS hπ w hw).2 c⟩)
  obtain ⟨C', hC', hq, hlen'⟩ := GlobalTheory.Cut.Peel.main D i 1 C (D.nd.Q i)
  refine ⟨C', hC'.trans hC, fun f hf => hfin f (hC' hf), ?_, hlen.trans (add_le_add le_rfl
    (hlen'.trans (add_le_add le_rfl (Finset.sum_le_sum fun q hq' => ?_))))⟩
  · intro v h1
    by_cases h3 : v ∈ D.nd.Q i
    · exact hq v h3
    refine resIne_eq_bot_of_le i (hC'.trans hC) ?_
    by_cases h2 : v ∈ D.nd.S i
    · rcases hSv v h2 with ⟨hqd, hu⟩ | hp
      · have h := GlobalTheory.T.length_inertia_restriction_cocycles_le D i r ρ π Xs S hr hS hπ v (Or.inl h2) hqd c
        rw [lenQ, length_quot_eq_zero_iff.mpr hu, nonpos_iff_eq_zero, Module.length_eq_zero_iff] at h
        exact Submodule.subsingleton_iff_eq_bot.mp h
      · exact GlobalTheory.T.inertiaCocycles_charBlock_otherTypePrime D i r ρ π Xs S hr hS hπ v h2 hp c
    · exact GlobalTheory.Proof.LocalGlobalSelmer.main D i r Xs S _ _ (inR'_one i r S) hU v h1 h2 h3
  · exact (length_mono (Submodule.map_mono hC)).trans
      (GlobalTheory.T.length_inertia_restriction_cocycles_le D i r ρ π Xs S hr hS hπ q (Or.inr hq') (hQ q hq') c)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem length_cocChi_le (hA : GlobalTheory.Published.GlobalArtinReciprocity) (eχ : ℕ) (hr : GoodR D.nd i r) (hS : GoodCongruenceObjects D.nd r ρ π S) (hπ : π ∈ Xs)
    (hU : UnrOut i r Xs)
    (hSv : ∀ v ∈ D.nd.S i, (QuadAt i r Xs v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Xs π v)
    (hQ : ∀ v ∈ D.nd.Q i, QuadAt i r Xs v) (c : Fin D.R.t)
    (hH : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), HfChar i w hw)
    (hL : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      LocBound i w hw r Xs (chiRatO D.nd i ((c : ℕ) + 1)) eχ) :
    Module.length (D.nd.O i) ↥(cocChi i r S Xs c) ≤
      (((placesOver D.host.E (D.nd.l i)).ncard * eχ : ℕ) : ℕ∞) * lenQ i ((D.nd.l i : ℕ) : D.nd.O i) +
        ((2 * lenQ i (del51 D.nd S S.π') + lenQ i ((D.nd.l i : ℕ) : D.nd.O i) *
            (if (c : ℕ) = 0 then ((padicValNat (D.nd.l i) (hE D.host) : ℕ) : ℕ∞)
              else Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) ((c : ℕ) : ℤ))) +
          ∑ q ∈ D.nd.Q i, lenQ i (D.nd.zeta i q - 1)) := by
  obtain ⟨C, hC, hfin, hunr, hlen⟩ := exists_fin_unr i r ρ π Xs S eχ hr hS hπ hU hSv hQ c hL
  refine hlen.trans (add_le_add le_rfl (add_le_add ?_ le_rfl))
  have hZ := hC.trans ((GlobalTheory.T.finiteQuotientCocycleSpan_rho_char_le_cocycles D i r ρ π Xs S hr hS hπ).2 c)
  by_cases hc : (c : ℕ) = 0
  · rw [if_pos hc]
    rw [hc, zero_add] at hZ hfin
    refine (GlobalTheory.UnramHom.length_le_classNumber hA D i C hZ fun v => ?_).trans le_add_self
    by_cases hv : v ∈ placesOver D.host.E (D.nd.l i)
    · exact GlobalTheory.CutTrivIne.main D i C v hv fun f hf => (hH v hv).2 (hfin f hf v hv)
    · exact hunr v hv
  · rw [if_neg hc]
    have h2 : 2 ≤ (c : ℕ) + 1 := by omega
    have ht : (c : ℕ) + 1 ≤ D.R.t := c.2
    have h := GlobalTheory.T.length_cyclotomic_block_cocycles_le_sha D i ((c : ℕ) + 1) C hZ h2 ht
      (fun f hf w hw => (hH w hw).1 _ (Finset.mem_Icc.mpr ⟨h2, ht⟩) (hfin f hf w hw)) hunr
    rw [Nat.add_sub_cancel] at h
    exact h.trans (add_le_add ((lenCob_mono i _ hC).trans
      ((GlobalTheory.T.length_coboundaries_among_block_cocycles_le D i r ρ π Xs S hr hS hπ).2 c)) le_rfl)

theorem sum_fin_ite {t : ℕ} (ht : 0 < t) (h : ℕ) (g : ℕ → ℕ) :
    ∑ c : Fin t, (if (c : ℕ) = 0 then h else g c) = h + ∑ e ∈ Finset.Ioo 0 t, g e := by
  rw [Fin.sum_univ_eq_sum_range (fun c => if c = 0 then h else g c) t]
  have : Finset.range t = insert 0 (Finset.Ioo 0 t) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [this, Finset.sum_insert (by simp), if_pos rfl]
  congr 1
  exact Finset.sum_congr rfl fun e he => if_neg (Finset.mem_Ioo.mp he).1.ne'

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

theorem main : GlobalTheory.Published.GlobalArtinReciprocity → GlobalCore := by
  intro hA D i r ρ π Xs eρ eχ S hr hS hZ hπ hN hU hSv hQ hl hsel hsha
  classical
  obtain ⟨L, hL⟩ := exists_length_quot (GlobalTheory.LenUnitPow.natCast_ne_zero (D.nd.l i) (O := D.nd.O i))
  have hL0 : L ≠ 0 := by
    rintro rfl
    exact GlobalTheory.LenUnitPow.natCast_not_isUnit (D.nd.l i) (O := D.nd.O i) (length_quot_eq_zero_iff.mp hL)
  obtain ⟨d, hd⟩ := exists_length_quot (del_ne_zero i r ρ π S hS)
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hsel)
  have hz : ∀ q ∈ D.nd.Q i, lenQ i (D.nd.zeta i q - 1) = ((lenQ i (D.nd.zeta i q - 1)).toNat : ℕ∞) := by
    intro q hq
    obtain ⟨n, hn⟩ := exists_length_quot (sub_ne_zero.mpr (hQ q hq).2)
    rw [lenQ, hn, ENat.toNat_coe]
  set z : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun q => (lenQ i (D.nd.zeta i q - 1)).toNat with hzdef
  set g : ℕ → ℕ := fun e => (Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ)).toNat with hg
  have hg' : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) = (g e : ℕ∞) :=
    fun e he => (ENat.coe_toNat (hsha e he).ne).symm
  have ht : 0 < D.R.t := D.R.t_odd.pos
  set n := (placesOver D.host.E (D.nd.l i)).ncard with hn
  set h := padicValNat (D.nd.l i) (hE D.host) with hh
  have hρ := length_cocRho_le i r ρ π Xs S eρ hr hS hπ hU fun w hw => (hl w hw).2.1
  have hχ : ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(cocChi i r S Xs c) ≤
      ((n * eχ * L + ((2 * d + L * (if (c : ℕ) = 0 then h else g c)) + ∑ q ∈ D.nd.Q i, z q) : ℕ) : ℕ∞) := by
    intro c
    refine (length_cocChi_le i r ρ π Xs S hA eχ hr hS hπ hU hSv (fun v hv => (hQ v hv).1) c
      (fun w hw => (hl w hw).1) fun w hw => (hl w hw).2.2 _
        (Finset.mem_Icc.mpr ⟨Nat.le_add_left _ _, c.2⟩)).trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl hz, lenQ, lenQ, hL, hd]
    by_cases hc : (c : ℕ) = 0
    · rw [if_pos hc, if_pos hc]
      push_cast
      rfl
    · rw [if_neg hc, if_neg hc, hg' c (Finset.mem_Ioo.mpr ⟨Nat.pos_of_ne_zero hc, c.2⟩)]
      push_cast
      rfl
  rw [lenQ, lenQ, hL, hd, ← hs] at hρ
  have htot := (GlobalTheory.T.length_heckeQuotient_le_cocycleSpan_determinant D i r ρ π Xs S hr hS hπ hZ hN).trans
    (add_le_add hρ (Finset.sum_le_sum fun c _ => hχ c))
  rw [← Nat.cast_sum, ← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add] at htot
  have hnat := ENat.toNat_le_of_le_coe htot
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    ← Finset.mul_sum, sum_fin_ite ht] at hnat
  have hvd : D.nd.vdel i = (d : ℚ) / L := by
    rw [← hS.2.2.2.2.2.2.2.2.2.2.1.2.2.2, lenUnit, hL, hd, ENat.toNat_coe, ENat.toNat_coe]
  have hsp : Br.sPi D.loc D.nbr i ρ π = (s : ℚ) / L := by
    rw [Br.sPi, lenUnit, hL, ← hs, ENat.toNat_coe, ENat.toNat_coe]
  have hsh : ∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ) =
      ((∑ e ∈ Finset.Ioo 0 D.R.t, g e : ℕ) : ℚ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun e he =>
      D.nd.sha_eq _ e (Finset.mem_Ioo.mp he).1 (Finset.mem_Ioo.mp he).2 _ (hg' e he)
  have hzq : ∑ q ∈ D.nd.Q i,
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1}) =
        ((∑ q ∈ D.nd.Q i, z q : ℕ) : ℚ) / L := by
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [lenUnit, hL, ENat.toNat_coe]
    rfl
  rw [hvd, hsp, hsh, hzq, vccOff, lenUnit, hL, ENat.toNat_coe]
  have hLq : (0 : ℚ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL0
  generalize (Module.length (D.nd.O i) (D.nd.O i ⧸ ccOff i Xs π)).toNat = a at hnat
  generalize ∑ e ∈ Finset.Ioo 0 D.R.t, g e = G at hnat
  generalize ∑ q ∈ D.nd.Q i, z q = Z at hnat
  have hq : (a : ℚ) ≤ _ := Nat.cast_le.mpr hnat
  rw [div_le_iff₀ hLq, Ranks.nV]
  push_cast at hq ⊢
  have hd0 : (0 : ℚ) ≤ ((D.R.r : ℚ) + D.R.t) * d := by positivity
  field_simp
  nlinarith [hq, hd0]

end GlobalTheory.CutCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftAllOfBlochKatoLiftingFamilyAtPlaceStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftAll_of_blochKatoLiftingFamilyAtPlace : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (e : ℕ), LiftFamW i w hw (fun x : ↥Xs => rTwO D.nd i r x) e → ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)), SubTw i r Xs M → ∀ (hM : Continuous fun g => M g) (a : ℕ) (x : Fin a → D.nd.X i), (∀ j, x j ∈ Xs) → ∀ (hc : ∀ j, Continuous fun g => Br.loc D.nbr i w hw (rTwO D.nd i r (x j)) g) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (hst : (∀ γ : GE D.nd, ∀ y ∈ Y, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)), BlochKatoDuality.LiftAll (Br.PD D.loc D.nbr i w hw) (GlobalTheory.Pass.LocDirect.Xgrep i w hw r x hc Y hst) (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM) e := by
  first | exact @GlobalTheory.Pass.LocDirect.liftAll_of_liftFamW | exact GlobalTheory.Pass.LocDirect.liftAll_of_liftFamW | (intros; apply GlobalTheory.Pass.LocDirect.liftAll_of_liftFamW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftAllSubSumsOfLiftFamilyMatrixFamilyStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftAll_subSums_of_liftFamily_matrixFamily : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (e : ℕ)
    (A A' : GRep G Qp LL O), LiftFam (O := O) PD Ms e → IsSubFam Ms A → IsSubFam Ms A' → BlochKatoDuality.LiftAll PD A A' e := by
  first | exact @GlobalTheory.Pass.LocDual.liftAll_of_liftFam | exact GlobalTheory.Pass.LocDual.liftAll_of_liftFam | (intros; apply GlobalTheory.Pass.LocDual.liftAll_of_liftFam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftableDescendsFromLargerCoefficientFieldStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftable_descends_from_larger_coefficientField : ∀ (l : ℕ) [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] {K₀ K B BdR : Type} [Field K₀] [Field K] [Algebra ℚ_[l] K₀] [Algebra ℚ_[l] K] [Algebra K₀ K] [IsScalarTower ℚ_[l] K₀ K] [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B] [Algebra K₀ B] [IsScalarTower ℚ_[l] K₀ B] [Algebra ℚ_[l] BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower ℚ_[l] K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower ℚ_[l] K₀ BdR] (PD : PeriodData G ℚ_[l] K₀ K B BdR) (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (k₁ k₂ : ℕ) (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L) (r : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1), (∀ a x, r (incl hL a * x) = a * r x) → r 1 = 1 → (∀ x ∈ OL LL', r x ∈ OL LL) → Continuous r → ∀ e : ℕ, (extHom hL hb₁ hb₂ F).LiftF PD e → F.LiftF PD e := by
  first | exact @GlobalTheory.CoefDescent.liftF_descends | exact GlobalTheory.CoefDescent.liftF_descends | (intros; apply GlobalTheory.CoefDescent.liftF_descends <;> assumption)
end

