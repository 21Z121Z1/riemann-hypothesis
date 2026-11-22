import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0876
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0030
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesCohomologous
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FrameCob

theorem res_comp {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  ext
  change ((X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom) (x : Γ(X, U)) = _
  rw [← Functor.map_comp]
  rfl

theorem comm_group_step {G : Type*} [CommGroup G] (a b c d e f g k : G) (A : a * b = c * d) (B : b = e * f)
    (C : d = g * k) : e * a * g⁻¹ * f = c * k := by
  subst B C
  calc e * a * g⁻¹ * f = g⁻¹ * (a * (e * f)) := by ac_rfl
    _ = g⁻¹ * (c * (g * k)) := by rw [A]
    _ = c * k := by rw [mul_left_comm c, inv_mul_cancel_left]

theorem frames_cohomologous : ∀ (X : Scheme.{0}) (C : Type) [Category.{0} C] (V : C → X.Opens)
    (hV : ∀ ⦃T T' : C⦄, (T ⟶ T') → V T' ≤ V T) (L L' : LB X)
    (u u' : ∀ (T T' : C) (_ : T ⟶ T'), Γ(X, V T')ˣ), L.IsLB → L'.IsLB → LBIso L L' →
    IsFrame L V hV u → IsFrame L' V hV u' →
    ∃ t : ∀ T : C, Γ(X, V T)ˣ, ∀ T T' a, u' T T' a * res (hV a) (t T) = t T' * u T T' a := by
  intro X C _ V hV L L' u u' hL hL' ⟨w, hw⟩ ⟨τ, hτg, hτ⟩ ⟨τ', hτ'g, hτ'⟩
  choose t ht htu using fun T => GlobalTheory.T.existsUnique_unit_ratio_generators_isomorphic_lineBundles X L L' (V T) w (τ T) (τ' T) hL hL' hw (hτg T) (hτ'g T)
  refine ⟨t, fun T T' a => ?_⟩
  have key : u' T T' a * res (hV a) (t T) * (u T T' a)⁻¹ = t T' := by
    refine htu T' _ (fun m m' => ?_)
    have hO : V T' ⊓ (L'.U m' ⊓ L.U m) ≤ V T ⊓ (L'.U m' ⊓ L.U m) := inf_le_inf_right _ (hV a)
    have A := congrArg (res hO) (ht T m m')
    have B := congrArg (res (inf_le_inf_left (V T') inf_le_left :
      V T' ⊓ (L'.U m' ⊓ L.U m) ≤ V T' ⊓ L'.U m')) (hτ' T T' a m')
    have C' := congrArg (res (inf_le_inf_left (V T') inf_le_right :
      V T' ⊓ (L'.U m' ⊓ L.U m) ≤ V T' ⊓ L.U m)) (hτ T T' a m)
    simp only [map_mul, map_inv, res_comp] at A B C' ⊢
    erw [res_comp] at A
    exact comm_group_step _ _ _ _ _ _ _ _ A B C'
  rw [← key, inv_mul_cancel_right]

end GlobalTheory.FrameCob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfPolarized
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG Polynomial GlobalTheory.SphPar GlobalTheory.CuspRep
open scoped TensorProduct

namespace GlobalTheory.SphGal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ParUEx {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (q n : ℕ) (lab : List ℤ → Prop)
    (c : List ℤ → ℂ) (s : Multiset ℂ) : Prop :=
  ∃ α : Fin (n / 2) → ℂ, (∀ i, α i ≠ 0) ∧ bcPar n α = s ∧
    ∀ φ : GU σ n → ℂ, IsSphericalU q α φ → ∀ d, lab d →
      hAct (KU σ n) (fun g : GU σ n => divInd (intL L) d (g : GL (Fin n) L)) φ 1 = c d * φ 1

section Global

variable {E : Type} [Field E] [NumberField E]

def ParGLEx (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (lab : List ℤ → Prop) (c : List ℤ → ℂ) (s : Multiset ℂ) : Prop :=
  ∃ α : Fin n → ℂ, (∀ i, α i ≠ 0) ∧ Finset.univ.val.map α = s ∧
    ∀ φ : GL (Fin n) (P.adicCompletion E) → ℂ, IsSpherical E P α φ → ∀ d, lab d →
      hAct (GLint (Fin n) (Ov E P)) (divInd (Ov E P) d) φ 1 = c d * φ 1

def IsParEx [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (lab : List ℤ → Prop) (c : List ℤ → ℂ) (s : Multiset ℂ) : Prop :=
  (Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal ≠ P.asIdeal → ParGLEx P n lab c s) ∧
  (Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal = P.asIdeal →
    ∀ (σ : P.adicCompletion E →+* P.adicCompletion E) (ϖ : P.adicCompletion E) (q : ℕ),
      IsConjAt P σ → IsUnramInv ϖ σ q → ParUEx σ q n lab c s)

end Global

def spehInf (d : ℕ) (A : Multiset ℂ) : Multiset ℂ :=
  ∑ j : Fin d, A.map (· + (((d : ℂ) - 1) / 2 - (j : ℕ)))

def spehSat (q d : ℕ) (B : Multiset ℂˣ) : Multiset ℂ :=
  ∑ j : Fin d, B.map fun b : ℂˣ => (b : ℂ) * (q : ℂ) ^ (-(((d : ℂ) - 1) / 2 - (j : ℕ)))

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  (M : DSModel V S)

def IsStableSub (W : Submodule ℂ (MMap M)) : Prop :=
  W ≤ Mult θ M ∅ (fun _ => 1) ∧ ∀ k ∈ GfC V, ∀ T ∈ W, heckeOn M {k} T ∈ W

def IsCuspQuot (W' W : Submodule ℂ (MMap M)) : Prop :=
  IsStableSub θ M W' ∧ IsStableSub θ M W ∧ W' < W ∧ ∀ U, IsStableSub θ M U → W' ≤ U → U ≤ W → U = W' ∨ U = W

def SphEig (W' W : Submodule ℂ (MMap M)) (P : HeightOneSpectrum (𝓞 D.host.E)) (c : List ℤ → ℂ) : Prop :=
  ∃ T ∈ W, T ∉ W' ∧ (∀ k ∈ GlobalTheory.Hk3.hyp V P, heckeOn M {k} T - T ∈ W') ∧
    ∀ d R, GlobalTheory.Hk3.SphOp V P d R → heckeOn M R T - c d • T ∈ W'

def HasBaseChange (W' W : Submodule ℂ (MMap M)) : Prop :=
  haveI := host_isCMField D.host
  ∃ (r : ℕ) (m d : Fin r → ℕ) (π : ∀ i, CuspSub D.host.E (m i)),
    (∀ i, 1 ≤ m i ∧ 1 ≤ d i ∧ (π i).IsCsd) ∧ ∑ i, m i * d i = V.rank ∧
    (∀ τ, ∃ A A' : Fin r → Multiset ℂ,
      (∀ i, (π i).HasInfChar (tauE D τ) (A i) ∧ (π i).HasInfChar (ComplexEmbedding.conjugate (tauE D τ)) (A' i)) ∧
      ∑ i, spehInf (d i) (A i) = Finset.univ.val.map (fun a => (M.lam τ a : ℂ)) ∧
      ∑ i, spehInf (d i) (A' i) = Finset.univ.val.map (fun a => -(M.lam τ a : ℂ))) ∧
    ∀ P c, SphEig M W' W P c → ∃ B : Fin r → Multiset ℂˣ, (∀ i, GlobalTheory.LFun.HasSatGL P ((π i).locRep P) (B i)) ∧
      IsParEx P V.rank (GlobalTheory.Hk3.IsLab V P) c (∑ i, spehSat (Formalism.ConjugateSelfDual.normV P) (d i) (B i))

def BaseChangeRegular : Prop :=
  ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (W' W : Submodule ℂ (MMap M)),
    IsInfFam θ → (∀ τ, Formalism.QuantumDeterminants.IsHCParam (M.lam τ)) → RegularWt M → IsCuspQuot θ M W' W → HasBaseChange M W' W

def GaloisOfPolarized : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (m : ℕ) (π : CuspSub E m) (χ : Formalism.L2.Host.HChar E) (u : ℝ),
    1 ≤ m → π.IsCsd → χ.IsAbsPow u → (CG.mk (π.twist χ)).IsRegAlg →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Formalism.ConjugateSelfDual.Qbar l ≃+* ℂ),
      ∃ ρ : Formalism.ConjugateSelfDual.G E (AlgebraicClosure E) →* GL (Fin m) (Formalism.ConjugateSelfDual.Qbar l), Continuous ρ ∧
        ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ B, GlobalTheory.LFun.HasSatGL w ((π.twist χ).locRep w) B →
          ∀ (A : ValuationSubring (AlgebraicClosure E)) (g : Formalism.ConjugateSelfDual.G E (AlgebraicClosure E)),
            Formalism.ConjugateSelfDual.IsPlaceOver (F := E) A w → Formalism.ConjugateSelfDual.IsFrob (F := E) A (Formalism.ConjugateSelfDual.normV w) g →
              ((ρ g⁻¹ : GL (Fin m) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin m) (Fin m) (Formalism.ConjugateSelfDual.Qbar l)).charpoly.map
                (ι : Formalism.ConjugateSelfDual.Qbar l →+* ℂ) = frobPoly (Formalism.ConjugateSelfDual.normV w) m (B.map fun b : ℂˣ => (b : ℂ))

theorem spehInf_one (A : Multiset ℂ) : spehInf 1 A = A := by simp [spehInf]

end GlobalTheory.SphGal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodFormsEqKilledByGroupAlgebra
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.CuspMult.EqCut

section Cosets

variable {Γ : Type} [Group Γ] {H J : Subgroup Γ}

theorem isDC_sub_iff (hJ : J ≤ H) (a : H) (R : Finset H) :
    Bridge.IsDC (J.subgroupOf H) a R ↔ Bridge.IsDC J (a : Γ) (R.map (Function.Embedding.subtype _)) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun b hb => ?_, ?_⟩
    · obtain ⟨b', hb', rfl⟩ := Finset.mem_map.1 hb
      obtain ⟨k₁, k₂, e⟩ := h1 b' hb'
      exact ⟨⟨k₁.1.1, k₁.2⟩, ⟨k₂.1.1, k₂.2⟩, congrArg Subtype.val e⟩
    · rintro g ⟨k₁, k₂, rfl⟩
      obtain ⟨b, ⟨hb, hb2⟩, hu⟩ := h2 _ ⟨⟨⟨k₁.1, hJ k₁.2⟩, k₁.2⟩, ⟨⟨k₂.1, hJ k₂.2⟩, k₂.2⟩, rfl⟩
      refine ⟨b.1, ⟨Finset.mem_map.2 ⟨b, hb, rfl⟩, hb2⟩, ?_⟩
      rintro y ⟨hy, hy2⟩
      obtain ⟨y', hy', rfl⟩ := Finset.mem_map.1 hy
      exact congrArg Subtype.val (hu y' ⟨hy', hy2⟩)
  · rintro ⟨h1, h2⟩
    refine ⟨fun b hb => ?_, ?_⟩
    · obtain ⟨k₁, k₂, e⟩ := h1 b.1 (Finset.mem_map.2 ⟨b, hb, rfl⟩)
      exact ⟨⟨⟨k₁.1, hJ k₁.2⟩, k₁.2⟩, ⟨⟨k₂.1, hJ k₂.2⟩, k₂.2⟩, Subtype.ext e⟩
    · rintro g ⟨k₁, k₂, rfl⟩
      obtain ⟨b, ⟨hb, hb2⟩, hu⟩ := h2 _ ⟨⟨k₁.1.1, k₁.2⟩, ⟨k₂.1.1, k₂.2⟩, rfl⟩
      obtain ⟨b', hb', rfl⟩ := Finset.mem_map.1 hb
      refine ⟨b', ⟨hb', hb2⟩, ?_⟩
      rintro y ⟨hy, hy2⟩
      exact Subtype.ext (hu y.1 ⟨Finset.mem_map.2 ⟨y, hy, rfl⟩, hy2⟩)

theorem exists_lift_of_isDC (hJ : J ≤ H) (a : H) (R' : Finset Γ) (h : Bridge.IsDC J (a : Γ) R') :
    ∃ R : Finset H, R.map (Function.Embedding.subtype _) = R' := by
  classical
  refine ⟨R'.subtype (· ∈ H), Finset.subtype_map_of_mem fun b hb => ?_⟩
  obtain ⟨k₁, k₂, rfl⟩ := h.1 b hb
  exact H.mul_mem (H.mul_mem (hJ k₁.2) a.2) (hJ k₂.2)

end Cosets

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem levChi_flag {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (hs : L.s = 0) (hQ : L.Q = ∅)
    (κ : GA D V) : levChi V β (flagL L) κ = 1 := by
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) (finE V κ)) = 1 := subgroupCharExtension_one_apply _ _
  have hs' : (flagL L).s = 0 := hs
  have hQ' : (flagL L).Q = ∅ := hQ
  unfold levChi levFn
  rw [h2, hs', hQ']
  simp

theorem levChi_flag1 {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (hs : L.s = 0) (hQ : L.Q = ∅)
    (κ : GA D V) : levChi V β (flag1L L) κ = 1 := by
  rw [← levChi_flag (β := β) hs hQ κ]
  unfold levChi
  rw [levFn_flag1]

theorem hasType_flag1 {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (P : LevelP L.Pg L.r ℂ)
    {F : GA D V → ℂ} (hF : HasType V β (withP L P) F) : HasType V β (flag1L L) F := by
  intro κ hκ h
  have e : rTup β L (finE V κ) = 1 := Subgroup.mem_bot.1 hκ.2.2
  have hm : κ ∈ levG V β (withP L P) := by
    refine ⟨hκ.1, hκ.2.1, ?_⟩
    show rTup β L (finE V κ) ∈ P.H
    rw [e]; exact P.H.one_mem
  rw [hF κ hm h]
  unfold levChi
  rw [levFn_withP, e, blockDiagonalExtendByOnePrimeField_one, one_mul, levFn_flag1]

theorem gaL_apply {β : GL (Fin V.rank) (EAf D)} {L : LevDat D.host.E ℂ V.rank} (hs : L.s = 0) (hQ : L.Q = ∅)
    {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) {F : GA D V → ℂ}
    (hF : HasType V β (flag1L L) F) (κ : G → GA D V) (hκ : ∀ g, IsLevelLift V β L (eG g) (κ g)) (h : GA D V) :
    gaL V β L eG c F h = ∑ g, c g * F (h * κ g) := by
  unfold gaL
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  have := level_action_spec hF ⟨κ g, hκ g⟩ (κ g) (hκ g) h
  rw [levChi_flag hs hQ, inv_one, one_mul] at this
  rw [← this]
  rfl

theorem alg_sum (M : DSModel V S) {ι : Type} (s : Finset ι) (κ : ι → GfC V) (c : ι → ℂ) (a : ℂ) (T : MMap M) :
    (finRep M).asAlgebraHom (∑ i ∈ s, MonoidAlgebra.single (κ i) (c i) - MonoidAlgebra.single 1 a) T = 0 ↔
      ∀ v x, ∑ i ∈ s, c i * T v (x * (κ i : GA D V)) = a * T v x := by
  rw [map_sub, map_sum, LinearMap.sub_apply, sub_eq_zero, LinearMap.sum_apply]
  simp only [Representation.asAlgebraHom_single, map_one, LinearMap.smul_apply, Module.End.one_apply]
  rw [MultilinearMap.ext_iff]
  refine forall_congr' fun v => ?_
  rw [funext_iff]
  refine forall_congr' fun x => ?_
  rw [MultilinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem alg_one (M : DSModel V S) (k : GfC V) (a : ℂ) (T : MMap M) :
    (finRep M).asAlgebraHom (MonoidAlgebra.single k 1 - MonoidAlgebra.single 1 a) T = 0 ↔
      ∀ v x, T v (x * (k : GA D V)) = a * T v x := by
  have := alg_sum M (Finset.univ : Finset Unit) (fun _ => k) (fun _ => 1) a T
  simpa only [Finset.univ_unique, Finset.sum_singleton, one_mul] using this

theorem mem_hPart (M : DSModel V S) (J : Subgroup (GA D V)) {Pl0 : Type} (ok : Set Pl0)
    (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) (T : MMap M) :
    T ∈ hPart M J ok pl q Sg ↔ ∀ P ∈ ok, ∀ k ≤ V.rank, ∀ α, IsHeckeAt V (pl P) k α → ∀ R, Bridge.IsDC J α⁻¹ R →
      ∀ v x, ∑ γ ∈ R, T v (x * γ) = ((Sg P).coeff k / ((-1) ^ k * (q P : ℂ) ^ (k * (k - 1) / 2))) * T v x := by
  unfold hPart
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, MultilinearMap.ext_iff, funext_iff]
  rfl

theorem good_hecke_eq_killed : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (P : LevelP L.Pg L.r ℂ) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]), L.s = 0 → L.Q = ∅ → LiftsExist V β L → goodPart θ M (levS V β (withP L P)) (levChi V β (withP L P)) (gaL V β L eG c) ⊓ hPart M (levG V β (flag1L L)) ok pl q Sg = allMaps θ M ⊓ killed (finRep M) (eqSet V β L eG c P ok pl q Sg) := by
  intro D V S θ M β L G _ _ eG c P Pl0 ok pl q Sg hs hQ hlift
  have hJ : levG V β (flag1L L) ≤ GfC V := fun _ h => h.1
  ext T
  rw [Submodule.mem_inf, Submodule.mem_inf, mem_goodPart, mem_killed, mem_hPart, GlobalTheory.MultMem.mem_mult_iff,
    GlobalTheory.MultMem.mem_mult_iff]
  constructor
  · rintro ⟨⟨hm, hg⟩, hh⟩
    refine ⟨⟨hm.aut, hm.cusp, fun _ _ h => h.elim, hm.equiv, hm.cont⟩, ?_⟩
    rintro x ((⟨k, hk, rfl⟩ | ⟨κ, hκ, rfl⟩) | ⟨P0, hP0, k, hk, α, R, hα, hR, rfl⟩)
    · exact (alg_one M k _ T).2 fun v x => hm.lev v k hk x
    · refine (alg_sum M _ κ c 1 T).2 fun v x => ?_
      have hF : HasType V β (flag1L L) (T v) := hasType_flag1 P fun k hk h => hm.lev v k hk h
      rw [← gaL_apply hs hQ eG c hF (fun g => κ g) hκ x, hg v, one_mul]
    · refine (alg_sum M R (fun γ => γ) (fun _ => 1) _ T).2 fun v x => ?_
      have := hh P0 hP0 k hk α hα _ ((isDC_sub_iff hJ α⁻¹ R).1 hR) v x
      rw [Finset.sum_map] at this
      simp only [one_mul]
      exact this
  · rintro ⟨hm, hk⟩
    have hlev : ∀ v, HasType V β (withP L P) (T v) := fun v k hkk x =>
      (alg_one M ⟨k, hkk.1⟩ _ T).1 (hk _ (Or.inl (Or.inl ⟨⟨k, hkk.1⟩, hkk, rfl⟩))) v x
    refine ⟨⟨⟨hm.aut, hm.cusp, fun v k hkk x => hlev v k hkk x, hm.equiv, hm.cont⟩, fun v => ?_⟩, ?_⟩
    · choose κ hκ using fun g => hlift (eG g)
      funext x
      rw [gaL_apply hs hQ eG c (hasType_flag1 P (hlev v)) κ hκ x]
      have := (alg_sum M Finset.univ (fun g => (⟨κ g, (hκ g).1⟩ : GfC V)) c 1 T).1
        (hk _ (Or.inl (Or.inr ⟨fun g => ⟨κ g, (hκ g).1⟩, hκ, rfl⟩))) v x
      rw [one_mul] at this
      exact this
    · intro P0 hP0 k hkr α hα R' hR' v x
      have hαf : α ∈ GfC V := by
        obtain ⟨e, ϖ, -, -, -, h⟩ := hα
        exact h.1
      obtain ⟨R, rfl⟩ := exists_lift_of_isDC hJ (⟨α, hαf⟩ : GfC V)⁻¹ R' hR'
      have hR := (isDC_sub_iff hJ (⟨α, hαf⟩ : GfC V)⁻¹ R).2 hR'
      have := (alg_sum M R (fun γ => γ) (fun _ => 1) _ T).1
        (hk _ (Or.inr ⟨P0, hP0, k, hkr, ⟨α, hαf⟩, R, hα, hR, rfl⟩)) v x
      simp only [one_mul] at this
      rw [Finset.sum_map]
      exact this

end GlobalTheory.CuspMult.EqCut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionExtendsAbelianSchemeDvr
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.LieExt

theorem prod_ofFn_eq {X : Type*} [Monoid X] {V : Type*} [AddCommMonoid V] (T : V → X)
    (h0 : T 0 = 1) (hadd : ∀ c c', T (c + c') = T c * T c') :
    ∀ {a : ℕ} (w : Fin a → V), (List.ofFn (fun i => T (w i))).prod = T (∑ i, w i)
  | 0, w => by simp [h0]
  | a + 1, w => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_eq T h0 hadd (fun i => w i.succ), Fin.sum_univ_succ, hadd]

theorem lie_ext : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (act : OActN D.O G) (ρ : W) (t : Fin D.a → (𝓞 D.F →+* W)), (∀ i, t i D.ω = ρ) → ρ ^ 2 - D.tr * ρ + D.nm = 0 → (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → IsUnit ((D.tr ^ 2 - 4 * D.nm : ℤ) : W) → (∀ (R' : Type) [CommRing R'] (β : L →+* R'), ∀ v : epsPtR (spMap (β.comp (algebraMap W L))) ⟶ G, IsTanScal act (spMap (β.comp (algebraMap W L))) (algebraMap (𝓞 D.F) D.O D.ω) (β (algebraMap W L ρ)) v → ∃ w : Fin D.a → (epsPtR (spMap (β.comp (algebraMap W L))) ⟶ G), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act (spMap (β.comp (algebraMap W L))) (algebraMap (𝓞 D.F) D.O c) (β (algebraMap W L (t i c))) (w i)) ∧ v = (List.ofFn w).prod) → (∀ (k : Type) [Field k] [IsAlgClosed k] (β : L →+* k) i, LieMult (act.toF D) (spMap (β.comp (algebraMap W L))) ((β.comp (algebraMap W L)).comp (t i)) D.m) → (∀ (R' : Type) [CommRing R'] (β : W →+* R'), ∀ v : epsPtR (spMap β) ⟶ G, IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O D.ω) (β ρ) v → ∃ w : Fin D.a → (epsPtR (spMap β) ⟶ G), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O c) (β (t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (β : W →+* k) i, LieMult (act.toF D) (spMap β) (β.comp (t i)) D.m := by
  intro p _ D W L _ _ _ _ _ _ G _ _ hab act ρ t htω hρ hcomax hdisc hgen hrank
  have hsm : Smooth G.hom := hab.smooth
  obtain ⟨n, M, hM⟩ := GlobalTheory.T.exists_tangent_coords_base_change_smooth_comm_group W G hsm

  have hT0 : ∀ {X : Type} [Group X] {V : Type} [AddCommMonoid V] (T : V → X),
      (∀ c c', T (c + c') = T c * T c') → T 0 = 1 := fun T h => by
    have := h 0 0
    rw [add_zero] at this
    exact mul_eq_left.mp this.symm
  obtain ⟨T₀, hinj₀, -, hadd₀, -, heq₀⟩ := hM W (RingHom.id W)
  have hmap : ∀ X : Matrix (Fin n) (Fin n) W, X.map (RingHom.id W) = X := fun X => by ext; simp
  have hext : ∀ X Y : Matrix (Fin n) (Fin n) W, (∀ c, T₀ (X.mulVec c) = T₀ (Y.mulVec c)) → X = Y := by
    intro X Y h
    ext i j
    have := congrFun (hinj₀ (h (Pi.single j 1))) i
    simpa [Matrix.mulVec_single_one] using this
  let Am : 𝓞 D.F → Matrix (Fin n) (Fin n) W := fun c => M (act.act (algebraMap (𝓞 D.F) D.O c))
  have hAm : ∀ c x, T₀ x ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T₀ ((Am c).mulVec x) := fun c x => by
    simpa [hmap] using heq₀ _ (act.hom _) x
  let A : 𝓞 D.F →+* Matrix (Fin n) (Fin n) W := RingHom.mk'
    { toFun := Am
      map_one' := hext _ _ fun x => by
        rw [Matrix.one_mulVec, ← hAm, map_one, act.one, Category.comp_id]
      map_mul' := fun c d => hext _ _ fun x => by
        rw [← hAm, map_mul, act.mul, ← Category.assoc, hAm, hAm, Matrix.mulVec_mulVec] }
    (fun c d => hext _ _ fun x => by
      show T₀ ((Am (c + d)).mulVec x) = T₀ ((Am c + Am d).mulVec x)
      rw [← hAm, map_add, act.add, MonObj.comp_mul, hAm, hAm, ← hadd₀, Matrix.add_mulVec])
  have hA : ∀ c, A c = M (act.act (algebraMap (𝓞 D.F) D.O c)) := fun c => rfl

  have tanT : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (T : (Fin n → R') → (epsPtR (spMap β) ⟶ G)),
      Function.Injective T →
      (∀ (s : R') c, (T (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (T c).left) →
      (∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map β).mulVec c)) →
      (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left =
        (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) →
      ∀ (c : 𝓞 D.F) (s : R') (x : Fin n → R'),
        IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O c) s (T x) ↔ ((A c).map β).mulVec x = s • x := by
    intro R' _ β T hinj hscale heq hrange c s x
    have hact : T x ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T (((A c).map β).mulVec x) :=
      heq _ (act.hom _) x
    constructor
    · rintro ⟨-, h2⟩
      refine hinj (Over.OverMorphism.ext ?_)
      rw [← hact, h2, hscale]
    · intro hx
      refine ⟨(hrange _).2 ⟨x, rfl⟩, ?_⟩
      rw [hact, hx, hscale]
  have hωroot : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hβL : (RingHom.id L).comp (algebraMap W L) = algebraMap W L := RingHom.id_comp _
  obtain ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ := GlobalTheory.T.eigenPart_splits_by_idempotent_matrices_domain W L (𝓞 D.F) n D.a A D.ω D.tr D.nm ρ t hωroot hρ htω hcomax hdisc
    (by
      intro v hv
      obtain ⟨T, hinj, hrange, hadd, hscale, heq⟩ := hM L ((RingHom.id L).comp (algebraMap W L))
      have tv := (tanT L _ T hinj hscale heq hrange D.ω ((RingHom.id L) (algebraMap W L ρ)) v).2
        (by rw [hβL, RingHom.id_apply]; exact hv)
      obtain ⟨w, hw, hvw⟩ := hgen L (RingHom.id L) (T v) tv
      have hy : ∀ i, ∃ y, w i = T y := fun i => by obtain ⟨y, h⟩ := (hrange _).1 (hw i 0).1; exact ⟨y, h.symm⟩
      choose y hy using hy
      refine ⟨y, fun i c => ?_, ?_⟩
      · have := (tanT L _ T hinj hscale heq hrange c _ (y i)).1 (by rw [← hy]; exact hw i c)
        rwa [hβL, RingHom.id_apply] at this
      · apply hinj
        rw [hvw, ← prod_ofFn_eq T (hT0 T hadd) hadd]
        exact congrArg List.prod (congrArg List.ofFn (funext hy)))
  have hmapsmul : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (s : W) (X : Matrix (Fin n) (Fin n) W),
      (s • X).map β = β s • X.map β := fun R' _ β s X => by ext; simp
  have heig : ∀ (R' : Type) [CommRing R'] (β : W →+* R') i c (x : Fin n → R'),
      ((A c).map β).mulVec (((Q i).map β).mulVec x) = β (t i c) • (((Q i).map β).mulVec x) := by
    intro R' _ β i c x
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hQ2, hmapsmul, Matrix.smul_mulVec]

  have rk : ∀ (k : Type) [Field k] (β : W →+* k) i,
      LieMult (act.toF D) (spMap β) (β.comp (t i)) D.m ↔ ((Q i).map β).rank = D.m := by
    intro k _ β i
    obtain ⟨T, hinj, hrange, hadd, hscale, heq⟩ := hM k β
    rw [GlobalTheory.T.lieMult_iff_finrank_common_eigenspace_coords W G (𝓞 D.F) (act.toF D) n k β T (fun c => (A c).map β) hinj hrange hadd hscale
      (fun c x => heq _ (act.hom _) x)]
    have hsub : (⨅ c, LinearMap.ker (Matrix.mulVecLin ((A c).map β) - (β.comp (t i)) c • LinearMap.id) :
        Submodule k (Fin n → k)) = LinearMap.range ((Q i).map β).mulVecLin := by
      ext y
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, LinearMap.mem_range, RingHom.comp_apply]
      constructor
      · intro h
        exact ⟨y, hQ4 k β i y h⟩
      · rintro ⟨z, rfl⟩ c
        exact heig k β i c z
    rw [hsub]
    rfl
  refine ⟨fun R' _ β v hv => ?_, fun k _ _ β i => ?_⟩
  · obtain ⟨T, hinj, hrange, hadd, hscale, heq⟩ := hM R' β
    obtain ⟨x, rfl⟩ := (hrange v).1 hv.1
    have hx := (tanT R' β T hinj hscale heq hrange D.ω (β ρ) x).1 hv
    refine ⟨fun i => T (((Q i).map β).mulVec x), fun i c =>
      (tanT R' β T hinj hscale heq hrange c _ _).2 (heig R' β i c x), ?_⟩
    rw [prod_ofFn_eq T (hT0 T hadd) hadd, ← hQ3 R' β x hx]
  · obtain ⟨r, hr⟩ := GlobalTheory.T.exists_rank_idempotent_matrix_local_ring_map_field W n (Q i) (hQ1 i)
    refine (rk k β i).2 ?_
    rw [hr, ← hr (AlgebraicClosure L) ((algebraMap L (AlgebraicClosure L)).comp (algebraMap W L))]
    exact (rk _ _ i).1 (hrank (AlgebraicClosure L) (algebraMap L (AlgebraicClosure L)) i)

end GlobalTheory.LieExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HxOfIsONFr
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem hx_of_isONFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ x : Frame X.Ψ r, IsONFr X x → x ∈ X.dom ∧ IsUnitFr X x ∧ ∀ z w : Fin g → ℂ, hx X bas idx x z w = ∑ j, (X.c (idx j).1 : ℂ) * z j * conj (w j) := by
  intro E _ _ _ r g n X bas idx hs _ x ho
  have hsg : ∀ a : ℕ, FD.sgn X.p0 a = 1 ∨ FD.sgn X.p0 a = -1 := fun a => by
    unfold FD.sgn; split_ifs <;> simp
  have e (τ : X.Ψ) (i : Fin (r + 1)) : dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    unfold dmin lminor
    rw [ho τ, sgnM, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    push_cast
    exact Fin.prod_univ_eq_prod_range (fun a => ((FD.sgn X.p0 a : ℝ) : ℂ)) (i : ℕ)
  have h0 (i : ℕ) : psgn X.p0 i ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => by rcases hsg a with h | h <;> rw [h] <;> norm_num
  have hd : x ∈ X.dom := by
    refine fun τ => ⟨fun h => ?_, fun i => ?_⟩
    · have h1 : FD.gram τ.1 X.Gm (mat x τ) =
          (mat x τ)ᵀ * X.Gm.map τ.1 * (mat x τ).map (starRingEnd ℂ) := by
        ext a b
        simp only [FD.gram, hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
          Matrix.map_apply, Finset.sum_mul]
        exact Finset.sum_comm
      have h2 := congrArg Matrix.det (h1.symm.trans (ho τ))
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, zero_mul, sgnM,
        Matrix.det_diagonal] at h2
      refine Finset.prod_ne_zero_iff.2 (fun a _ => ?_) h2.symm
      rcases hsg a with h | h <;> rw [h] <;> norm_num
    · rw [e, Complex.ofReal_re]
      exact mul_self_pos.2 (h0 _)
  refine ⟨hd, fun τ i => ?_, (GlobalTheory.Dict.hx_ortho E r X g bas idx hs x hd ho).1⟩
  rw [e, psgn]
  push_cast
  rw [norm_prod]
  exact Finset.prod_eq_one fun a _ => by rcases hsg a with h | h <;> rw [h] <;> simp

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelicCharacterEqProdUnramifiedValueZpowStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idelicCharacter_eq_prod_unramifiedValue_zpow : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → ∀ (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) (m : HeightOneSpectrum (𝓞 D.host.E) → ℤ), (∀ Q ∈ S, χ.UnrAt Q ∧ Valued.v (ι (finPart D (x : AE D)) Q) = WithZero.exp (-m Q)) → (∀ Q, Q ∉ S → ι (finPart D (x : AE D)) Q = 1) → ((c x : Circle) : ℂ) = ((∏ Q ∈ S, χ.val Q ^ m Q : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.CharUnramVal.char_eq_prod_val_zpow | exact GlobalTheory.CharUnramVal.char_eq_prod_val_zpow | (intros; apply GlobalTheory.CharUnramVal.char_eq_prod_val_zpow <;> assumption)
end

