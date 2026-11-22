import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.WeightedChainData
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0043
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0428
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0082

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyFactorizationSemisimpleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_factorization_semisimple : ∀ (D : D7), Formalism.MainNotions.SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (x : D.nd.X i) (r : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r → ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), IsSSRep (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) ρ) → (∀ g, ((r g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).charpoly = ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly * ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i))) → GlobalTheory.LocalInv.Cont D.nd i ρ := by
  first | exact @GlobalTheory.SSComplement.cont | exact GlobalTheory.SSComplement.cont | (intros; apply GlobalTheory.SSComplement.cont <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficieStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_weilDeligne_potSemistable_enlarge_coefficients : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {m : ℕ} {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1) (r₁ : ↥(Dec (F := E) A) →* GL (Fin m) ↥L₁.1), IsPst P (Bw.repE L₁ r₁) → IsPst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) → ∀ σ : ↥(Weil h), WD.charPol (wdPst P ι Bw h hj (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁))) σ = WD.charPol (wdPst P ι Bw h hj (Bw.repE L₁ r₁)) σ := by
  first | exact @GlobalTheory.Pst.EnlargeCoeff.charPol_wdPst_enlarge | exact GlobalTheory.Pst.EnlargeCoeff.charPol_wdPst_enlarge | (intros; apply GlobalTheory.Pst.EnlargeCoeff.charPol_wdPst_enlarge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresDoubleCosetAdjointCommute
section
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory

theorem classPres_dcOp_adjoint_commute : ∀ {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : ClassPres ι S σ ρ J χ) (L : Subgroup G) (x : G) (A A' B : Finset G) (T T' U : Module.End K S.Forms), (∀ γ u u', inner ℂ (ρ γ u) (ρ γ u') = inner ℂ u u') → (∀ k, ‖(χ k : ℂ)‖ = 1) → (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l) → (∀ k : J, (k : G) ∈ L → χ k = 1) → (∀ a ∈ A, a ∈ L) → (∀ a ∈ A', a ∈ L) → IsDC J x A → IsDC J x⁻¹ A' → (∀ f : S.Forms, P.ext ((T f : S.Forms) : S.Cl → S.V) = dcOp A (P.ext (f : S.Cl → S.V))) → (∀ f : S.Forms, P.ext ((T' f : S.Forms) : S.Cl → S.V) = dcOp A' (P.ext (f : S.Cl → S.V))) → (∀ f : S.Forms, P.ext ((U f : S.Forms) : S.Cl → S.V) = dcOp B (P.ext (f : S.Cl → S.V))) → (∀ f g : S.Forms, S.csum ((T f : S.Forms) : S.Cl → S.V) (g : S.Cl → S.V) = S.csum (f : S.Cl → S.V) ((T' g : S.Forms) : S.Cl → S.V)) ∧ ((∀ F ∈ AdForms ι ρ J χ, dcOp A (dcOp B F) = dcOp B (dcOp A F)) → Commute T U) := by
  intro G Γ W K _ _ _ _ _ _ _ ι S σ ρ J χ P L x A A' B T T' U hρ hχ hJ hχL hA hA' hx hx' hT hT' hU
  obtain ⟨hmem, hiso, -, -, hinj⟩ := classPres_basic ι S σ ρ J χ P
  refine ⟨fun f g => ?_, fun hc => ?_⟩
  · apply σ.injective
    rw [← hiso, ← hiso, hT, hT']
    exact GlobalTheory.T.adelicInner_doubleCosetOp_adjoint ι ρ J L χ P.y x A A' hρ hχ P.reps
      (fun c => Finite.of_equiv _ (P.stabI c).toEquiv) hJ hχL hA hA' hx hx' _ (hmem f) _ (hmem g)
  · refine LinearMap.ext fun f => hinj ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, P.extL_apply, P.extL_apply, hT, hU, hU, hT]
    exact hc _ (hmem f)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffRenameEquiv
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Classical

namespace GlobalTheory.InertCompare

section Series

variable {l : ℕ} [Fact l.Prime]

variable {d : ℕ} [NeZero d]

def twoCopies (d : ℕ) : ZMod d × Bool ≃ ZMod d ⊕ ZMod d where
  toFun x := if x.2 then Sum.inr x.1 else Sum.inl x.1
  invFun := Sum.elim (fun s => (s, false)) (fun s => (s, true))
  left_inv := by rintro ⟨s, _ | _⟩ <;> rfl
  right_inv := by rintro (s | s) <;> rfl

end Series

section Product

variable (D : D7) (l : ℕ) [Fact l.Prime]

end Product

end GlobalTheory.InertCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefficientFieldEnlargementLocChiCyclotomicStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficientFieldEnlargement_locChi_cyclotomic : ∀ {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw), (∀ z : ℚ_[D.nd.l i], C.inc (algebraMap _ _ z) = algebraMap _ _ z) → ∀ s, C.inc ((Br.locChi D.nbr i w hw (epsU D.nd i) s : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) = ((cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 s : (↥C.LL.1)ˣ) : ↥C.LL.1) := by
  first | exact @GlobalTheory.HTW.Rec.enl_locChi_epsU | exact GlobalTheory.HTW.Rec.enl_locChi_epsU | (intros; apply GlobalTheory.HTW.Rec.enl_locChi_epsU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompactSpaceMaximalCompactUnitaryInfiniteStatement
section
open GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactSpace_maximalCompact_unitary_infinite : ∀ (E : Type) [Field E] (a : ℕ), CompactSpace (Kinf E a) := by
  first | exact @GlobalTheory.KinfCompactness.compactSpace_Kinf | exact GlobalTheory.KinfCompactness.compactSpace_Kinf | (intros; apply GlobalTheory.KinfCompactness.compactSpace_Kinf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeInterior
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

namespace GlobalTheory

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} in

theorem _root_.GlobalTheory.phiT_add_smul_homAt (K : Type) [Field K]
    {ST SG SG' S : Finset (HeightOneSpectrum (𝓞 E))}
    (d : _root_.Formalism.L2.Col.Deco E a ST SG) (d' : _root_.Formalism.L2.Col.Deco E b ST SG') (hd' : d'.Ok) (hS : ST ⊆ S) (c : 𝓞 E)
    (hc : ∀ P : ST, c ∈ P.1.asIdeal) (x y₀ : _root_.Formalism.L2.Col.HomE E a b) (hy : y₀ ∈ _root_.Formalism.L2.Col.homAt S d.N d'.N) :
    _root_.Formalism.L2.Col.phiT K d d' (x + c • y₀) = _root_.Formalism.L2.Col.phiT K d d' x := by
  unfold _root_.Formalism.L2.Col.phiT
  have key : ∀ P : ST, ∀ y ∈ d.at P,
      ((x + c • y₀) y ∈ d'.at P ∧ d'.f P ((x + c • y₀) y) = d.f P y) ↔
        (x y ∈ d'.at P ∧ d'.f P (x y) = d.f P y) := by
    intro P y hyP
    have hy0 : y₀ y ∈ d'.at P := hy P.1 (hS P.2) y hyP
    have hcy : c • y₀ y ∈ d'.at P := Submodule.smul_mem _ c hy0
    have hf0 : d'.f P (c • y₀ y) = 0 := by
      rw [hd'.f_smul P c _ hy0, Ideal.Quotient.eq_zero_iff_mem.2 (hc P), zero_mul]
    have happ : (x + c • y₀) y = x y + c • y₀ y := rfl
    rw [happ, Submodule.add_mem_iff_left _ hcy]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [← h2, hd'.f_add P _ h1 _ hcy, hf0, add_zero]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [hd'.f_add P _ h1 _ hcy, hf0, add_zero, h2]⟩
  have hiff : (∀ P : ST, ∀ y ∈ d.at P,
      (x + c • y₀) y ∈ d'.at P ∧ d'.f P ((x + c • y₀) y) = d.f P y) ↔
      (∀ P : ST, ∀ y ∈ d.at P, x y ∈ d'.at P ∧ d'.f P (x y) = d.f P y) :=
    forall_congr' fun P => forall₂_congr fun y hyP => key P y hyP
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.1 h1) h2
  · exact absurd (hiff.2 h2) h1
  · rfl

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} in
omit [NumberField E] [StarRing E] in
theorem _root_.GlobalTheory.inFr_add (f : _root_.Formalism.L2.Col.Sp E a ≃ₗ[E] _root_.Formalism.L2.Col.Sp E a) (f' : _root_.Formalism.L2.Col.Sp E b ≃ₗ[E] _root_.Formalism.L2.Col.Sp E b)
    (x y : _root_.Formalism.L2.Col.HomE E a b) :
    _root_.Formalism.L2.Col.inFr f f' (x + y) = _root_.Formalism.L2.Col.inFr f f' x + _root_.Formalism.L2.Col.inFr f f' y := by
  unfold _root_.Formalism.L2.Col.inFr
  rw [LinearMap.add_comp, LinearMap.comp_add]

open NumberField IsDedekindDomain in
variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} in

theorem _root_.GlobalTheory.intAt_inFr_smul_homAt {S : Finset (HeightOneSpectrum (𝓞 E))}
    {N : Submodule (𝓞 E) (_root_.Formalism.L2.Col.Sp E a)}
    {N' : Submodule (𝓞 E) (_root_.Formalism.L2.Col.Sp E b)} {P : HeightOneSpectrum (𝓞 E)} (hP : P ∈ S)
    (f : _root_.Formalism.L2.Col.Sp E a ≃ₗ[E] _root_.Formalism.L2.Col.Sp E a) (f' : _root_.Formalism.L2.Col.Sp E b ≃ₗ[E] _root_.Formalism.L2.Col.Sp E b)
    (hf : ∀ x, f x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ x ∈ _root_.Formalism.L2.Col.stdAt E a P)
    (hf' : ∀ x, f' x ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' ↔ x ∈ _root_.Formalism.L2.Col.stdAt E b P)
    (c r : 𝓞 E) (e : E) (he : e ≠ 0) (hc : algebraMap (𝓞 E) E c = e * algebraMap (𝓞 E) E r)
    (y₀ : _root_.Formalism.L2.Col.HomE E a b) (hy : y₀ ∈ _root_.Formalism.L2.Col.homAt S N N') (s : Fin a) (l : Fin b) :
    _root_.Formalism.L2.Col.IntAt P (e⁻¹ * _root_.Formalism.L2.Col.inFr f f' (c • y₀) (Pi.single s 1) l) := by
  have hv : (Pi.single s 1 : _root_.Formalism.L2.Col.Sp E a) ∈ _root_.Formalism.L2.Col.stdAt E a P := by
    refine ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩
    rw [one_smul]
    refine Submodule.mem_pi.2 fun i _ => ?_
    by_cases h : i = s
    · subst h
      rw [Pi.single_eq_same]
      exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]
      exact Submodule.zero_mem _
  have hz : y₀ (f (Pi.single s 1)) ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' := hy P hP _ ((hf _).2 hv)
  have hw : f'.symm (y₀ (f (Pi.single s 1))) ∈ _root_.Formalism.L2.Col.stdAt E b P :=
    (hf' _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hz)
  obtain ⟨t, ht, htw⟩ := hw
  have hl : (t • f'.symm (y₀ (f (Pi.single s 1)))) l ∈ (1 : Submodule (𝓞 E) E) :=
    Submodule.mem_pi.1 htw l (Set.mem_univ l)
  obtain ⟨r', hr'⟩ := Submodule.mem_one.1 hl
  have hval : _root_.Formalism.L2.Col.inFr f f' (c • y₀) (Pi.single s 1) l =
      algebraMap (𝓞 E) E c * f'.symm (y₀ (f (Pi.single s 1))) l := by
    show (f'.symm (c • y₀ (f (Pi.single s 1)))) l = _
    rw [← algebraMap_smul E c (y₀ (f (Pi.single s 1))), map_smul, Pi.smul_apply, smul_eq_mul]
  unfold _root_.Formalism.L2.Col.IntAt
  refine ⟨r * r', t, ht, ?_⟩
  rw [hval, hc, map_mul, hr', Pi.smul_apply, Algebra.smul_def]
  calc _ = (e⁻¹ * e) * (algebraMap (𝓞 E) E t * (algebraMap (𝓞 E) E r *
        f'.symm (y₀ (f (Pi.single s 1))) l)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ he, one_mul]; ring

end General

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumSupportDivLatticeFinal
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

namespace GlobalTheory.SuppTop

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem intAt_nat (P : HeightOneSpectrum (𝓞 E)) (c : ℕ) : IntAt P (c : E) := by
  simpa using IntAt.coe P (c : 𝓞 E)

theorem intAt_sum {ι : Type} (P : HeightOneSpectrum (𝓞 E)) (s : Finset ι) (f : ι → E) (h : ∀ i ∈ s, IntAt P (f i)) :
    IntAt P (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IntAt P) (fun _ _ ha hb => ha.add hb) (by simpa using intAt_nat P 0) h

theorem smul_mem_of_inFr {a b : ℕ} (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E a))
    (N' : Submodule (𝓞 E) (Sp E b)) (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b)
    (hf : ∀ y, f y ∈ localization₂ P.asIdeal N ↔ y ∈ stdAt E a P) (hf' : ∀ y, f' y ∈ localization₂ P.asIdeal N' ↔ y ∈ stdAt E b P)
    (c : ℕ) (x : HomE E a b) (h : ∀ s l, IntAt P ((c : E) * inFr f f' x (Pi.single s 1) l)) :
    ∀ y ∈ localization₂ P.asIdeal N, (c : E) • x y ∈ localization₂ P.asIdeal N' := by
  intro y hy
  have hv : f.symm y ∈ stdAt E a P := (hf _).1 (by simpa using hy)
  have hv' : ∀ i, IntAt P (f.symm y i) := (mem_localization_standardLattice P _).1 hv
  have e : (c : E) • x y = f' ((c : E) • inFr f f' x (f.symm y)) := by simp [inFr]
  rw [e, hf']
  refine (mem_localization_standardLattice P _).2 fun l => ?_
  have e2 : inFr f f' x (f.symm y) = ∑ s, f.symm y s • inFr f f' x (Pi.single s 1) := by
    conv_lhs => rw [pi_eq_sum_univ' (f.symm y)]
    simp only [map_sum, map_smul]
  rw [e2]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine intAt_sum P _ _ fun s _ => ?_
  rw [mul_left_comm]
  exact (hv' s).mul (h s l)

theorem entB_zero {N' N : ℕ} (q k₀ c' n' n : ℕ) (hc : c' = 0) (ex' ex : ℕ → ℕ) (x : HomE E N' N) (p p' : ℕ) (hp : p < n)
    (hp' : p' < n') :
    LocE.entB q k₀ c' n' 0 n ex' ex x p p' = Loc.atN (x (Loc.eN E N' p')) p := by
  subst hc
  have h1 : ∀ m s, LocE.fIdx k₀ 0 m s = s := by
    intro m s
    unfold LocE.fIdx
    split_ifs <;> omega
  simp [LocE.entB, h1, LocE.scE, hp, hp']

end General

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem intAt_of_phiTop (sharp : Bool) (m2 : ℕ) (hm : R.m = m2 + 2) (P : HeightOneSpectrum (𝓞 X.E))
    (z : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0)) (hz : PhiTop Ch mu sharp m2 P z ≠ 0)
    (p p' : ℕ) (hp : p < R.N R.m - 1) (hp' : p' < R.N (m2 + 1)) :
    IntAt P (Loc.atN (z (Loc.eN X.E _ p')) p) := by
  have hc : cOf R (m2 + 1) = 0 := by unfold cOf; omega
  have ha : p' < R.r + (R.m - 1) * R.t := by
    have : R.m - 1 = m2 + 1 := by omega
    unfold Ranks.N at hp'
    unfold Ranks.r
    rw [this]
    have : (m2 + 1) * (R.t + 1) = (m2 + 1) * R.t + (m2 + 1) := by ring
    omega
  unfold PhiTop at hz
  split_ifs at hz
  · unfold LocE.PhiGS at hz
    simp only at hz
    split_ifs at hz with h
    · have := h.1 p p' hp ha
      rwa [entB_zero _ _ _ _ _ hc _ _ _ _ _ hp hp'] at this
    · exact absurd rfl hz
  · unfold LocE.PhiG at hz
    simp only at hz
    split_ifs at hz with h
    · have := h.1 p p' hp ha
      rwa [entB_zero _ _ _ _ _ hc _ _ _ _ _ hp hp'] at this
    · exact absurd rfl hz
  · unfold LocE.PhiQ at hz
    split_ifs at hz with h
    · have := h.1 p p' hp (by omega)
      rwa [entB_zero _ _ _ _ _ hc _ _ _ _ _ hp hp'] at this
    · exact absurd rfl hz

theorem intAt_of_ftY {n : ℕ} (P : rowSG Pr sel mu) (η : Sp X.E n →ₗ[X.E] X.E) (y' : Sp X.E n)
    (h : ftY sel mu cst P η y' ≠ 0) (s : Fin n) : IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η (Pi.single s 1)) := by
  unfold ftY at h
  split_ifs at h with h1 h2 h3
  · have := (intAt_nat P.1 (qOf P.1 ^ cst.M)).mul (h2 s)
    simpa using this
  · exact absurd rfl h
  · exact h3 s
  · exact absurd rfl h

end Chain

end GlobalTheory.SuppTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumSupportDivLatticeInterior
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

namespace GlobalTheory.Proof.datum_support_div_lattice_interior

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem intAt_sum {P : HeightOneSpectrum (𝓞 E)} {ι : Type} (s : Finset ι) (f : ι → E)
    (h : ∀ i ∈ s, IntAt P (f i)) : IntAt P (∑ i ∈ s, f i) := by
  refine Finset.sum_induction f (IntAt P) (fun _ _ ha hb => ha.add hb) ?_ h
  simpa using IntAt.coe P 0

theorem smul_mem_of_frames {a b : ℕ} (P : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) (Sp E a))
    (M' : Submodule (𝓞 E) (Sp E b)) (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b)
    (hf : ∀ x, f x ∈ M ↔ x ∈ stdAt E a P) (hf' : ∀ x, f' x ∈ M' ↔ x ∈ stdAt E b P)
    (x : HomE E a b) (c : E) (h : ∀ s l, IntAt P (c * inFr f f' x (Pi.single s 1) l)) :
    ∀ y ∈ M, c • x y ∈ M' := by
  classical
  intro y hy
  obtain ⟨z, rfl⟩ := f.surjective y
  have hz : ∀ i, IntAt P (z i) := (mem_localization_standardLattice P z).1 ((hf z).1 hy)
  have e : c • x (f z) = f' (c • inFr f f' x z) := by simp [inFr]
  rw [e, hf']
  refine (mem_localization_standardLattice P _).2 fun l => ?_
  have hz' : z = ∑ s, z s • (Pi.single s (1 : E) : Sp E a) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  have e2 : (c • inFr f f' x z) l = ∑ s, z s * (c * inFr f f' x (Pi.single s 1) l) := by
    conv_lhs => rw [hz']
    simp only [map_sum, map_smul, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e2]
  exact intAt_sum _ _ fun s _ => (hz s).mul (h s l)

end General

end GlobalTheory.Proof.datum_support_div_lattice_interior
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DecorationLiftStdLatticeReduction
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory

theorem decoSet_liftFr_lifts_level :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (ST SG : Finset (HeightOneSpectrum (𝓞 E)))
      (d : DecoSet E n ST SG) (w : SG),
      (∀ x, d.1.liftFr w x ∈ d.1.at w.1 ↔ x ∈ stdAt E n w.1) ∧
        ∀ x ∈ stdAt E n w.1, d.1.be w (d.1.liftFr w x) = redV w.1 x :=
  fun _ _ _ _ _ _ _ d w => GlobalTheory.TopStep.liftFr_spec d.2 w

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndSpannedOfIsIrrSubOfIsAlgClosedStatement
section
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endSpanned_of_isIrrSub_of_isAlgClosed' : ∀ {Γ E : Type} [Group Γ] [Field E] [IsAlgClosed E] {a : ℕ} (σ : Γ →* GL (Fin a) E) (U : Submodule E (Fin a → E)), IsIrrSub σ U → EndSpanned σ U := by
  first | exact @GlobalTheory.SplitField.endSpanned_of_isIrrSub_of_isAlgClosed | exact GlobalTheory.SplitField.endSpanned_of_isIrrSub_of_isAlgClosed | (intros; apply GlobalTheory.SplitField.endSpanned_of_isIrrSub_of_isAlgClosed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalTranslationCompCommutingOperatorStatement
section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localTranslation_comp_commuting_operator : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : GlobalTheory.CuspRep.CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (o : GlobalTheory.CuspRep.Op E a), ∃ (g : GL (Fin a) (w.adicCompletion E)) (T : Module.End ℂ π.V), (∀ h, T ∘ₗ π.locRep w h = π.locRep w h ∘ₗ T) ∧ π.op o = π.locRep w g ∘ₗ T := by
  first | exact @GlobalTheory.LocFactor.exists_locRep_comp | exact GlobalTheory.LocFactor.exists_locRep_comp | (intros; apply GlobalTheory.LocFactor.exists_locRep_comp <;> assumption)
end

