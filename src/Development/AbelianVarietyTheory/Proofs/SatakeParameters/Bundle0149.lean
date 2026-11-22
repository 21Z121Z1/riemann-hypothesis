import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0120
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0071
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0085
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0089
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.PlaceInjective
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0003
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesTrivial
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0013
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0019
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0076
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0145
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0123
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriVectorTwoBlockProductPermValueFirst

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGaloisRepInducedMatches
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
  GlobalTheory.WeilDeligne
open TensorProduct Module

namespace GlobalTheory.Pst.QuotLine

theorem enl_isPst : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) {m : ℕ} {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1) (r₁ : ↥Gw →* GL (Fin m) ↥L₁.1), IsPst P (Bw.repE L₁ r₁) → IsPst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) := GlobalTheory.T.isPotentiallySemistable_coefficientField_enlarge

theorem enl_charPol : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {m : ℕ} {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1) (r₁ : ↥(Dec (F := E) A) →* GL (Fin m) ↥L₁.1), IsPst P (Bw.repE L₁ r₁) → IsPst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) → ∀ σ : ↥(Weil h), WD.charPol (wdPst P ι Bw h hj (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁))) σ = WD.charPol (wdPst P ι Bw h hj (Bw.repE L₁ r₁)) σ := GlobalTheory.T.charpoly_weilDeligne_potSemistable_enlarge_coefficients

theorem rank_Dpst_le : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l), IsDomain (Bst P) → (∀ (K : FinExt l) (b b' : Bst P), b ≠ 0 → (∀ g : ↥(GK K), b * actSt P (g : GQ l) b' = actSt P (g : GQ l) b * b') → ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ b' = algebraMap ↥(MaximalUnramifiedExtension l) (Bst P) c * b) → ∀ {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional ℚ_[l] V] (ρ : Representation LL ↥(GK K) V), Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) ≤ finrank ℚ_[l] V := GlobalTheory.T.finrank_dpst_unramified_le_dim_representation

theorem exists_dmap_ne_zero : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL], (∀ (W : Type) [AddCommGroup W] [Module LL W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] LL W] [FiniteDimensional ℚ_[l] W] (ρW : Representation LL ↥(GK K) W), Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρW) ≤ finrank ℚ_[l] W) → ∀ {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional LL V] [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V'] {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'} {f : V →ₗ[LL] V'} (hf : ∀ g v, f (ρ g v) = ρ' g (f v)), IsPst P ρ → f ≠ 0 → ∃ x : ↥(Dpst P ρ), GlobalTheory.Pst.DpstMap.dmap P hf x ≠ 0 := GlobalTheory.T.dpst_rank_le_dimension

theorem dmap_phiD_pow {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL]
    [Algebra ℚ_[l] LL] {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'} {f : V →ₗ[LL] V'}
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (n : ℕ) (x : ↥(Dpst P ρ)) :
    DpstMap.dmap P hf ((phiD P ρ ^ n) x) = (phiD P ρ' ^ n) (DpstMap.dmap P hf x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', pow_succ', End.mul_apply, End.mul_apply, DpstMap.dmap_phiD, ih]

theorem charpoly_dvd_of_map {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E]
    [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {LL : FinExt l}
    (hb : ∀ (W : Type) [AddCommGroup W] [Module ↥LL.1 W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] ↥LL.1 W]
      [FiniteDimensional ℚ_[l] W] (ρW : Representation ↥LL.1 ↥(GK Bw.Kw) W),
      Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρW) ≤ finrank ℚ_[l] W)
    {V V' : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V']
    [FiniteDimensional ↥LL.1 V']
    {ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V} {ρ' : Representation ↥LL.1 ↥(GK Bw.Kw) V'} {f : V →ₗ[↥LL.1] V'}
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (hf0 : f ≠ 0) (hV : IsPst P ρ) (hV' : IsPst P ρ')
    (hd : finrank ↥LL.1 V' = 1) (σ : ↥(Weil h)) :
    haveI := hV.finite; haveI := hV'.finite
    (wdRho P ι Bw h hj ρ' σ).charpoly ∣ (wdRho P ι Bw h hj ρ σ).charpoly := by
  haveI := hV.finite
  haveI := hV'.finite
  haveI := LL.2
  have key := exists_dmap_ne_zero P hb hf hV hf0
  obtain ⟨x, hx⟩ := key
  have key2 : ∃ n : ℕ, wdMk P ι ρ' ((phiD P ρ' ^ n) (DpstMap.dmap P hf x)) ≠ 0 := by
    by_contra hcon
    exact hx (GlobalTheory.PstFaithful.eq_zero_of_wdMk_phiD_pow l P ι Bw.Kw LL V' ρ' (DpstMap.dmap P hf x)
      fun n => not_not.mp fun hn => hcon ⟨n, hn⟩)
  obtain ⟨n, hn⟩ := key2
  have hne : DpstMap.wdLin P ι hf (wdMk P ι ρ ((phiD P ρ ^ n) x)) ≠ 0 := by
    rwa [DpstMap.wdLin_mk, dmap_phiD_pow]
  have hdim : finrank ℂ (WDSpace P ι ρ') = 1 := by
    rw [GlobalTheory.Pst.LetterDim.finrank_wdSpace l P ι Bw.Kw LL V' ρ' hV', hd]
  have hsurj : Function.Surjective (DpstMap.wdLin P ι hf) := by
    have h1 := Submodule.finrank_le (LinearMap.range (DpstMap.wdLin P ι hf))
    have h2 : finrank ℂ (LinearMap.range (DpstMap.wdLin P ι hf)) ≠ 0 := by
      rw [Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
      intro h0
      exact hne ((LinearMap.congr_fun h0 _).trans (LinearMap.zero_apply _))
    exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq (by omega))
  exact DpstMap.charpoly_dvd_of_surjective _ hsurj _ _ (DpstMap.wdLin_wdRho P ι Bw h hj hf σ)

theorem charpoly_dvd_one_field {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E]
    [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {LL : FinExt l} {a : ℕ}
    (hb : ∀ (W : Type) [AddCommGroup W] [Module ↥LL.1 W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] ↥LL.1 W]
      [FiniteDimensional ℚ_[l] W] (ρW : Representation ↥LL.1 ↥(GK Bw.Kw) W),
      Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρW) ≤ finrank ℚ_[l] W)
    (r : ↥(Dec (F := E) A) →* GL (Fin a) ↥LL.1) (c : ↥(Dec (F := E) A) →* GL (Fin 1) ↥LL.1)
    (hr : IsPst P (Bw.repE LL r)) (hc : IsPst P (Bw.repE LL c)) (v : Fin a → ↥LL.1) (hv : v ≠ 0)
    (hrel : ∀ g, Matrix.vecMul v (r g : Matrix (Fin a) (Fin a) ↥LL.1) = (c g : Matrix (Fin 1) (Fin 1) ↥LL.1) 0 0 • v)
    (σ : ↥(Weil h)) :
    haveI := hr.finite; haveI := hc.finite
    (wdRho P ι Bw h hj (Bw.repE LL c) σ).charpoly ∣ (wdRho P ι Bw h hj (Bw.repE LL r) σ).charpoly := by
  have hf : ∀ g x, (Matrix.of fun (_ : Fin 1) i => v i).mulVecLin (Bw.repE LL r g x) =
      Bw.repE LL c g ((Matrix.of fun (_ : Fin 1) i => v i).mulVecLin x) := by
    intro g x
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    change dotProduct v (Matrix.mulVec (r (Bw.e.symm g) : Matrix (Fin a) (Fin a) ↥LL.1) x) =
      ∑ j : Fin 1, (c (Bw.e.symm g) : Matrix (Fin 1) (Fin 1) ↥LL.1) 0 j * dotProduct v x
    rw [Matrix.dotProduct_mulVec, hrel, smul_dotProduct, Fin.sum_univ_one, smul_eq_mul]
  have hf0 : (Matrix.of fun (_ : Fin 1) i => v i).mulVecLin ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    intro h0
    have := congrFun (LinearMap.congr_fun h0 (Pi.single i 1)) 0
    change dotProduct v (Pi.single i 1) = 0 at this
    rw [dotProduct_single, mul_one] at this
    exact hi this
  exact charpoly_dvd_of_map P ι Bw h hj hb hf hf0 hr hc (Module.finrank_fin_fun _) σ

theorem roots_le_of_models {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E]
    [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {LL L₁ L₂ : FinExt l} {a : ℕ}
    (hb : ∀ (W : Type) [AddCommGroup W] [Module ↥LL.1 W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] ↥LL.1 W]
      [FiniteDimensional ℚ_[l] W] (ρW : Representation ↥LL.1 ↥(GK Bw.Kw) W),
      Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρW) ≤ finrank ℚ_[l] W)
    (h₁ : L₁.1 ≤ LL.1) (h₂ : L₂.1 ≤ LL.1) (r₁ : ↥(Dec (F := E) A) →* GL (Fin a) ↥L₁.1)
    (c₂ : ↥(Dec (F := E) A) →* GL (Fin 1) ↥L₂.1) (hp₁ : IsPst P (Bw.repE L₁ r₁)) (hp₂ : IsPst P (Bw.repE L₂ c₂))
    (v : Fin a → ↥LL.1) (hv : v ≠ 0)
    (hrel : ∀ g, Matrix.vecMul v (mapRep (IntermediateField.inclusion h₁).toRingHom r₁ g : Matrix (Fin a) (Fin a) ↥LL.1) =
      (mapRep (IntermediateField.inclusion h₂).toRingHom c₂ g : Matrix (Fin 1) (Fin 1) ↥LL.1) 0 0 • v)
    (σ : ↥(Weil h)) :
    (WD.charPol (wdPst P ι Bw h hj (Bw.repE L₂ c₂)) σ).roots ≤ (WD.charPol (wdPst P ι Bw h hj (Bw.repE L₁ r₁)) σ).roots := by
  have hp₁' := enl_isPst P Bw h₁ r₁ hp₁
  have hp₂' := enl_isPst P Bw h₂ c₂ hp₂
  haveI := hp₁'.finite
  haveI := hp₂'.finite
  have k1 := enl_charPol P ι Bw h hj h₁ r₁ hp₁ hp₁' σ
  have k2 := enl_charPol P ι Bw h hj h₂ c₂ hp₂ hp₂' σ
  have k3 := DpstMap.charPol_wdPst P ι Bw h hj (Bw.repE LL (mapRep (IntermediateField.inclusion h₁).toRingHom r₁)) hp₁' σ
  have k4 := DpstMap.charPol_wdPst P ι Bw h hj (Bw.repE LL (mapRep (IntermediateField.inclusion h₂).toRingHom c₂)) hp₂' σ
  have k5 := charpoly_dvd_one_field P ι Bw h hj hb _ _ hp₁' hp₂' v hv hrel σ
  have e1 := k1.symm.trans k3
  have e2 := k2.symm.trans k4
  exact (congrArg Polynomial.roots e2).trans_le
    ((Polynomial.roots.le_of_dvd (LinearMap.charpoly_monic _).ne_zero k5).trans_eq (congrArg Polynomial.roots e1.symm))

theorem quotient_char_eig : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {a : ℕ} (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (c : ↥(Dec (F := E) A) →* GL (Fin 1) (Om l)), IsPstAt P Bw r → IsPstAt P Bw c → ∀ v : Fin a → Om l, v ≠ 0 → (∀ g, Matrix.vecMul v (r g : Matrix (Fin a) (Fin a) (Om l)) = (c g : Matrix (Fin 1) (Fin 1) (Om l)) 0 0 • v) → ∀ σ : ↥(Weil h), (WD.charPol (wdAt P ι Bw h hj c) σ).roots ≤ (WD.charPol (wdAt P ι Bw h hj r) σ).roots := by
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w O _ _ _ Bw h hj a r c hr hc v hv hrel σ
  have hS' := GlobalTheory.Pst.stRegular l P AI hT
  obtain ⟨hdom, hfrac, -⟩ := hS'
  have hr' := wdAt_of_isPstAt ι Bw h hj hr
  obtain ⟨L₁, r₁, hm₁, hp₁, e₁⟩ := hr'
  have hc' := wdAt_of_isPstAt ι Bw h hj hc
  obtain ⟨L₂, c₂, hm₂, hp₂, e₂⟩ := hc'
  have hLL : ∃ LL : FinExt l, L₁.1 ≤ LL.1 ∧ L₂.1 ≤ LL.1 ∧ ∀ i, v i ∈ LL.1 := by
    haveI : Finite (Set.range v) := Set.finite_range v
    refine ⟨supExt (supExt L₁ L₂) ⟨IntermediateField.adjoin ℚ_[l] (Set.range v),
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩,
      le_sup_left.trans le_sup_left, le_sup_right.trans le_sup_left, fun i => ?_⟩
    exact (le_sup_right : IntermediateField.adjoin ℚ_[l] (Set.range v) ≤ _)
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  rcases hLL with ⟨LL, h₁, h₂, hvL⟩
  have hm₁' := hm₁.enlarge h₁
  have hm₂' := hm₂.enlarge h₂
  have hv' : ∃ v' : Fin a → ↥LL.1, ∀ i, (v' i : Om l) = v i := ⟨fun i => ⟨v i, hvL i⟩, fun _ => rfl⟩
  rcases hv' with ⟨v', hv'⟩
  have er : ∀ g i j, ((r g : Matrix (Fin a) (Fin a) (Om l)) i j) =
      (((mapRep (IntermediateField.inclusion h₁).toRingHom r₁ g : Matrix (Fin a) (Fin a) ↥LL.1) i j : ↥LL.1) : Om l) :=
    fun g i j => by rw [← hm₁'.2]; rfl
  have ec : ∀ g i j, ((c g : Matrix (Fin 1) (Fin 1) (Om l)) i j) =
      (((mapRep (IntermediateField.inclusion h₂).toRingHom c₂ g : Matrix (Fin 1) (Fin 1) ↥LL.1) i j : ↥LL.1) : Om l) :=
    fun g i j => by rw [← hm₂'.2]; rfl
  have hv0 : v' ≠ 0 := fun h0 => hv (funext fun i => by rw [← hv' i, h0]; rfl)
  have hrel' : ∀ g, Matrix.vecMul v' (mapRep (IntermediateField.inclusion h₁).toRingHom r₁ g : Matrix (Fin a) (Fin a) ↥LL.1) =
      (mapRep (IntermediateField.inclusion h₂).toRingHom c₂ g : Matrix (Fin 1) (Fin 1) ↥LL.1) 0 0 • v' := by
    intro g
    funext j
    apply Subtype.val_injective
    have := congrFun (hrel g) j
    simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] at this ⊢
    simp only [er, ec, ← hv'] at this
    push_cast
    exact this
  haveI := LL.2
  have hb : ∀ (W : Type) [AddCommGroup W] [Module ↥LL.1 W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] ↥LL.1 W]
      [FiniteDimensional ℚ_[l] W] (ρW : Representation ↥LL.1 ↥(GK Bw.Kw) W),
      Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρW) ≤ finrank ℚ_[l] W :=
    fun W _ _ _ _ _ ρW => rank_Dpst_le P hdom hfrac ρW
  have key := roots_le_of_models P ι Bw h hj hb h₁ h₂ r₁ c₂ hp₁ hp₂ v' hv0 hrel' σ
  rw [e₁, e₂]
  exact key

end GlobalTheory.Pst.QuotLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuIntOfCharTied
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

namespace GlobalTheory.MuIntegral

theorem muInt_of_charTied : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch), Formalism.L2.Host.NCharTied D C nch Tp → MuInt D.nd D.naut := by
  intro D C nch Tp hT i τ z hz
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hjj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hmu := hT.muC i j hjj
  haveI : IsTotallyComplex D.host.E := D.sp.cm.cmUnram.1
  obtain ⟨n, hn, ho⟩ := Tp.xi_fin (D.nd.mu i)
  have hinf : (Tp.tup (D.nd.mu i) j).HasInfQ (Formalism.L2.Host.embPsi D.host) (fun g => -Formalism.L2.Host.eExp D j g) :=
    (C.isMu0 j).inf.mul_triv (GlobalTheory.TypeValues.inf_eq_one _ hn ho)
  rw [← hmu] at hinf
  have key := hT.infG _ _ hinf
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.VolRatioCheck.place_bijective D).2 (InfinitePlace.mk τ)
  obtain ⟨m, hm⟩ := (D.hc (D.eTau.symm (D.eTau ρ))).e_int j
  have hm' : Formalism.L2.Host.eExp D j (D.eTau ρ) = m := hm
  rcases InfinitePlace.mk_eq_iff.1 hρ with h | h
  · have ht : τ = Formalism.L2.Host.embPsi D.host (D.eTau ρ) := h.symm
    rw [ht, (key (D.eTau ρ)).1] at hz
    refine ⟨-m, ?_⟩
    simp only [Multiset.mem_singleton, Set.mem_singleton_iff] at hz
    rw [hz, hm']; push_cast; ring
  · have ht : τ = (starRingEnd ℂ).comp (Formalism.L2.Host.embPsi D.host (D.eTau ρ)) := by
      rw [← h]; ext x; rfl
    rw [ht, (key (D.eTau ρ)).2] at hz
    refine ⟨m, ?_⟩
    simp only [Multiset.mem_singleton, Set.mem_singleton_iff] at hz
    rw [hz, hm']; push_cast; ring

end GlobalTheory.MuIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NumberFieldCompletionRingEquivOfDenseUnramified
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt
open WithZero

namespace GlobalTheory.DenseCompl

theorem completion_ringEquiv_of_dense : ∀ {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (hc : IsAdicComplete (Ideal.span {(p : W)}) W) (ρ : E →+* Qq) (h1 : ∀ x : 𝓞 E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) (h2 : ∀ (y : W) (n : ℕ), ∃ (x : 𝓞 E) (z : W), ρ x = algebraMap W Qq (y + (p : W) ^ n * z)), ∃ φ : P.adicCompletion E ≃+* Qq, (∀ x : E, φ (algebraMap E (P.adicCompletion E) x) = ρ x) ∧ (∀ n : ℕ, IsOpen {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)}) ∧ ∀ U ∈ nhds (0 : P.adicCompletion E), ∃ n : ℕ, {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)} ⊆ U := by
  intro E _ _ P W Qq _ _ _ _ _ _ p hp hc ρ h1 h2
  classical
  set v := closedPoint W
  have hint : ∀ x : 𝓞 E, v.valuation Qq (ρ x) = P.valuation E x := by
    intro x
    obtain ⟨y, hy, -⟩ := h1 x
    have hx : (x : E) = algebraMap (𝓞 E) E x := rfl
    rw [hy, hx, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    have key : ∀ k : ℕ, P.intValuation x ≤ exp (-(k : ℤ)) ↔ v.intValuation y ≤ exp (-(k : ℤ)) := by
      intro k
      rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
        asIdeal_eq_span hp v, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact GlobalTheory.T.mem_pow_heightOneIdeal_iff_dvd_embedding P p hp ρ h1 h2 x y k hy
    exact le_antisymm (le_of_forall_le_exp (P.intValuation_le_one x) fun k hk => (key k).1 hk)
      (le_of_forall_le_exp (v.intValuation_le_one y) fun k hk => (key k).2 hk)
  have hval : ∀ x : E, v.valuation Qq (ρ x) = P.valuation E x := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
    rw [map_div₀, map_div₀, map_div₀]
    exact congrArg₂ (· / ·) (hint a) (hint b)
  have hf : ∀ x : E, Valued.v (((algebraMap Qq (v.adicCompletion Qq)).comp ρ) x) = P.valuation E x :=
    fun x => by rw [RingHom.comp_apply, GlobalTheory.Idele.valued_algebraMap, hval]
  obtain ⟨ψ, -, hψ, hψv⟩ := exists_extension P v _ hf
  have hψW : ∀ y : W, algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq y) ∈ Set.range ψ := by
    intro y
    choose x z hxz using fun n : ℕ => h2 y n
    let u : ℕ → P.adicCompletion E := fun n => algebraMap E _ (x n : E)
    have hu : ∀ m n : ℕ, n ≤ m → Valued.v (u m - u n) ≤ exp (-(n : ℤ)) := by
      intro m n hnm
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
      simp only [u]
      rw [← map_sub, GlobalTheory.Idele.valued_algebraMap, ← hval, map_sub, hxz, hxz, ← map_sub]
      refine (exists_eq_pow_mul_iff hp v _ n).1 ⟨(p : W) ^ k * z (n + k) - z n, ?_⟩
      congr 1
      ring
    obtain ⟨t, ht⟩ := GlobalTheory.Idele.exists_limit P u hu
    refine ⟨t, ?_⟩
    rw [← sub_eq_zero]
    refine Valued.v.zero_iff.1 (eq_zero_of_forall_le_exp fun n => ?_)
    have e : ψ t - algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq y) =
        ψ (t - u n) + algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq ((p : W) ^ n * z n)) := by
      rw [map_sub, hψ, RingHom.comp_apply, hxz, map_add, map_add]
      ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · rw [hψv]
      exact ht n
    · rw [GlobalTheory.Idele.valued_algebraMap]
      exact (exists_eq_pow_mul_iff hp v _ n).1 ⟨z n, rfl⟩
  have hι := GlobalTheory.T.surjective_algebraMap_adicCompletion_complete_dvr (Qq := Qq) (p : W) hp hc v
  have hsurj : Function.Surjective ψ := by
    intro a
    obtain ⟨q, rfl⟩ := hι a
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W) q
    obtain ⟨s, hs⟩ := hψW a
    obtain ⟨t, ht⟩ := hψW b
    exact ⟨s / t, by rw [map_div₀, hs, ht, map_div₀]⟩
  let eψ := RingEquiv.ofBijective ψ ⟨ψ.injective, hsurj⟩
  let eι := RingEquiv.ofBijective (algebraMap Qq (v.adicCompletion Qq))
    ⟨(algebraMap Qq (v.adicCompletion Qq)).injective, hι⟩
  have hφ : ∀ z, algebraMap Qq (v.adicCompletion Qq) ((eψ.trans eι.symm) z) = ψ z :=
    fun z => eι.apply_symm_apply (ψ z)
  have hS : ∀ (n : ℕ) (z : P.adicCompletion E),
      (∃ w : W, (eψ.trans eι.symm) z = algebraMap W Qq ((p : W) ^ n * w)) ↔ Valued.v z ≤ exp (-(n : ℤ)) := by
    intro n z
    rw [exists_eq_pow_mul_iff hp v, ← GlobalTheory.Idele.valued_algebraMap v, hφ, hψv]
  refine ⟨eψ.trans eι.symm, fun x => ?_, fun n => ?_, fun U hU => ?_⟩
  · apply (algebraMap Qq (v.adicCompletion Qq)).injective
    rw [hφ, hψ]
    rfl
  · have e : {z : P.adicCompletion E | ∃ w : W, (eψ.trans eι.symm) z = algebraMap W Qq ((p : W) ^ n * w)} =
        {z | Valued.v z ≤ exp (-(n : ℤ))} := Set.ext fun z => hS n z
    rw [e]
    exact GlobalTheory.Idele.isOpen_valued_le P (-(n : ℤ))
  · obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hU
    obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt
      (γ := MonoidWithZeroHom.ValueGroup₀.embedding γ.1) (by simp)
    refine ⟨n, fun z hz => hγ ?_⟩
    have hz' := (hS n z).1 hz
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    exact hz'.trans_lt hn

end GlobalTheory.DenseCompl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PartsAdjointIntertwinerEqJointEigenspaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem parts_of_adjoint_lift : ∀ {X E I : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (Θ : X →ₗ[ℂ] E) (op : I → Module.End ℂ X) (h : I → Module.End ℂ E), ∀ {C : Type} (Ec : C → Submodule ℂ E) (lab : C → I → ℂ), (∀ i u, Θ (op i u) = h i (Θ u)) → (∀ i, Commute (op i) (LinearMap.adjoint (op i))) → (∀ i, Commute (h i) (LinearMap.adjoint (h i))) → Formalism.L2.Col.PairComm op → (⨆ c, Ec c) = ⊤ → (∀ c, ∀ w ∈ Ec c, ∀ i, h i w = lab c i • w) → (∀ c, Ec c ≠ ⊥ → ∃ w ∈ Ec c, LinearMap.adjoint Θ w ≠ 0) → Formalism.L2.Col.PairComm h ∧ ∀ Q : (I → ℂ) → Prop, (∀ c, Ec c ≠ ⊥ → ((Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigSum op Q ↔ Q (lab c))) ∧ (⨆ (c : C) (_ : Ec c ≠ ⊥ ∧ (Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigSum op Q), Ec c) = Formalism.L2.Col.eigSum h Q := by
  intro X E I _ _ _ _ _ _ Θ op h C Ec lab hint hn hn' hc htop hh hne
  have hcomm : Formalism.L2.Col.PairComm h := by
    intro i j
    refine GlobalTheory.EigTransfer.linearMap_ext_of_iSup_eq_top Ec htop (h i * h j) (h j * h i) fun c w hw => ?_
    simp only [Module.End.mul_apply, hh c w hw, map_smul, smul_smul, mul_comm]
  have hup : ∀ c, (Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigAt op (lab c) := by
    rintro c _ ⟨w, hw, rfl⟩
    exact Formalism.L2.Col.mem_eigAt_of_forall_apply fun i =>
      GlobalTheory.T.eigenvector_adjoint_intertwiner_normal_operators Θ op h hint hn hn' i (lab c i) w (hh c w hw i)
  have hiff : ∀ (Q : (I → ℂ) → Prop) c, Ec c ≠ ⊥ →
      ((Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigSum op Q ↔ Q (lab c)) := by
    intro Q c hcne
    constructor
    · intro hle
      by_contra hq
      obtain ⟨w, hw, hw0⟩ := hne c hcne
      have hm : LinearMap.adjoint Θ w ∈ (Ec c).map (LinearMap.adjoint Θ) := ⟨w, hw, rfl⟩
      have hd := Formalism.L2.Col.disjoint_eigSum hc (C := fun x => ¬ Q x) (C' := Q) fun x hx => hx
      exact hw0 ((Submodule.disjoint_def.1 hd) _
        (Formalism.L2.Col.eigAt_le_eigSum (C := fun x => ¬ Q x) hq (hup c hm)) (hle hm))
    · intro hq
      exact (hup c).trans (Formalism.L2.Col.eigAt_le_eigSum hq)
  refine ⟨hcomm, fun Q => ⟨fun c hcne => hiff Q c hcne, ?_⟩⟩
  have hle : ∀ P : (I → ℂ) → Prop, (⨆ (c : C) (_ : P (lab c)), Ec c) ≤ Formalism.L2.Col.eigSum h P := fun P =>
    iSup₂_le fun c hq w hw => Formalism.L2.Col.eigAt_le_eigSum hq
      (Formalism.L2.Col.mem_eigAt_of_forall_apply fun i => hh c w hw i)
  have hsup : (⨆ (c : C) (_ : Q (lab c)), Ec c) ⊔ (⨆ (c : C) (_ : ¬ Q (lab c)), Ec c) = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun c => ?_
    by_cases hq : Q (lab c)
    · exact le_sup_of_le_left (le_iSup₂_of_le (f := fun c (_ : Q (lab c)) => Ec c) c hq le_rfl)
    · exact le_sup_of_le_right (le_iSup₂_of_le (f := fun c (_ : ¬ Q (lab c)) => Ec c) c hq le_rfl)
  have hd : Disjoint (⨆ (c : C) (_ : ¬ Q (lab c)), Ec c) (Formalism.L2.Col.eigSum h Q) :=
    (Formalism.L2.Col.disjoint_eigSum hcomm (C := fun x => ¬ Q x) (C' := Q) fun x hx => hx).mono_left
      (hle fun x => ¬ Q x)
  have hQ : (⨆ (c : C) (_ : Q (lab c)), Ec c) = Formalism.L2.Col.eigSum h Q := by
    have := sup_inf_assoc_of_le (⨆ (c : C) (_ : ¬ Q (lab c)), Ec c) (hle Q)
    rw [hsup, top_inf_eq, hd.eq_bot, sup_bot_eq] at this
    exact this.symm
  rw [← hQ]
  apply le_antisymm
  · refine iSup₂_le fun c hcq => ?_
    exact le_iSup₂_of_le (f := fun c (_ : Q (lab c)) => Ec c) c ((hiff Q c hcq.1).1 hcq.2) le_rfl
  · refine iSup₂_le fun c hq => ?_
    by_cases hb : Ec c = ⊥
    · rw [hb]; exact bot_le
    · exact le_iSup₂_of_le (f := fun c (_ : Ec c ≠ ⊥ ∧ (Ec c).map (LinearMap.adjoint Θ) ≤ Formalism.L2.Col.eigSum op Q) => Ec c)
        c ⟨hb, (hiff Q c hb).2 hq⟩ le_rfl

end GlobalTheory.Hk3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualOne
section
noncomputable section

namespace GlobalTheory.Hk3.HoweG

open Matrix

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def adj (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (x : Matrix (Fin n') (Fin n) L) :
    Matrix (Fin n) (Fin n') L :=
  ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ x * (JT : Matrix (Fin n') (Fin n') L)

def HomA (σ : L →+* L) {n n' : ℕ} (JS : GL (Fin n) L) (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L) : Prop :=
  (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) → ∀ i, (y *ᵥ u) i ∈ Formalism.UG.intL L) ∧
    ∀ w : Fin n' → L, (∀ i, w i ∈ Formalism.UG.intL L) → ∀ i, (y *ᵥ (adj σ JS JT x *ᵥ w)) i ∈ Formalism.UG.intL L

def GramEq (σ : L →+* L) {n n' : ℕ} (JT : GL (Fin n') L) (x y : Matrix (Fin n') (Fin n) L) : Prop :=
  ∀ m m' : Fin n → L, (∀ i, m i ∈ Formalism.UG.intL L) → (∀ i, m' i ∈ Formalism.UG.intL L) → ∀ c ∈ Formalism.UG.intL L,
    (∀ i, (x *ᵥ (c • m)) i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ (c • m')) i ∈ Formalism.UG.intL L) →
      c * (Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (y *ᵥ m) (y *ᵥ m') -
        Formalism.UG.hform σ (JT : Matrix (Fin n') (Fin n') L) (x *ᵥ m) (x *ᵥ m')) ∈ Formalism.UG.intL L

def SelfDual (σ : L →+* L) {n : ℕ} (JS : GL (Fin n) L) (a : GL (Fin n) L) : Prop :=
  (∀ i j, (Formalism.UG.cT σ (a : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * (a : Matrix (Fin n) (Fin n) L)) i j ∈
      Formalism.UG.intL L) ∧
    ∀ i j, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      Formalism.UG.cT σ ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L

end GlobalTheory.Hk3.HoweG

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalFactorsOfParahoricVectorTwoBlockProductStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_factors_of_parahoricVector_twoBlockProduct : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ₁ : Representation ℂ (GL (Fin r) k) V) (σ₂ : Representation ℂ (GL (Fin t) k) W) (f : _), IsParahoricVec χ (prod₂ σ₁ σ₂) f → f.1.1 1 ≠ 0 → IsSpherical σ₁ ∧ IsSpherical (twist σ₂ (detChar (Fin t) χ⁻¹)) := by
  first | exact @GlobalTheory.ParahoricSph.isSpherical_of_isParahoricVec | exact GlobalTheory.ParahoricSph.isSpherical_of_isParahoricVec | (intros; apply GlobalTheory.ParahoricSph.isSpherical_of_isParahoricVec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriTorusCharVectorOfParahoricDetCharVectStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameIwahoriTorusCharVector_of_parahoricDetCharVector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin (r + t)) k) V) (v : V), IsTame χ → IsParahoricVec χ π v → IsIwVec (Fin.append (fun _ : Fin r => (1 : kˣ →* ℂˣ)) (fun _ : Fin t => χ)) π v := by
  first | exact @GlobalTheory.TameParahoric.isIwVec_of_isParahoricVec | exact GlobalTheory.TameParahoric.isIwVec_of_isParahoricVec | (intros; apply GlobalTheory.TameParahoric.isIwVec_of_isParahoricVec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriVectorTwoBlockProductPermValueFirstStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameIwahoriVector_twoBlockProduct_perm_value_first : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (θ : Fin (r + t) → kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ₁ : Representation ℂ (GL (Fin r) k) V) (σ₂ : Representation ℂ (GL (Fin t) k) W) (f : _) (w : Equiv.Perm (Fin (r + t))), IsIwVec θ (prod₂ σ₁ σ₂) f → f.1.1 (GlobalTheory.Parabolic.permGL k w) ≠ 0 → ∃ (s : Equiv.Perm (Fin r)) (y : V), y ≠ 0 ∧ IsIwVec (fun i => θ (w.symm (Fin.castAdd t (s i)))) σ₁ y := by
  first | exact @GlobalTheory.TameIwahori.PermCell.exists_isIwVec_fst | exact GlobalTheory.TameIwahori.PermCell.exists_isIwVec_fst | (intros; apply GlobalTheory.TameIwahori.PermCell.exists_isIwVec_fst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.VacuumTranslateRelationMapPreservingVacuaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumTranslate_relation_map_preserving_vacua : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), LocPair ϖ σ q δ JS JT ψ ρ ω → ∀ φ : M →ₗ[ℂ] M, (∀ s, LocVac ρ s → LocVac ρ (φ s)) → ∀ f : Matrix (Fin n') (Fin n) L →₀ M, (∀ x, LocVac ρ (f x)) → (f.sum fun x m => ρ x m) = 0 → (f.sum fun x m => ρ x (φ m)) = 0 := by
  first | exact @GlobalTheory.Hk3.locVac_rel_map | exact GlobalTheory.Hk3.locVac_rel_map | (intros; apply GlobalTheory.Hk3.locVac_rel_map <;> assumption)
end

