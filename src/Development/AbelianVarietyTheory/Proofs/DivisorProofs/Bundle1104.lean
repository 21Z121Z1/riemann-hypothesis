import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousBicharacterWeilSetup
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Bundle0001
import GroundTheory.GlobalFields.IdeleGroups.UnitBound
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0870
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0804
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0805
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HermitianHassePrincipleHolds
import Formalism.LocalToGlobal.IndefiniteReal.DatumF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHWOfFd
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem exists_isHW_of_fd : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act →
    (∀ v, v ∈ ⨆ μ : Ix p q → ℚ, wtSub act μ) → ∀ U : Submodule ℂ V, U ≠ ⊥ →
    FiniteDimensional ℂ U → KStable act U → ∃ (μ : Ix p q → ℚ) (v : V), v ∈ U ∧ IsHW act μ v := by
  intro p q V _ _ act hL hd U hU hfd hK
  exact GlobalTheory.BlockReps.exists_hw (fun Y Z _ _ => hL Y Z) hK (fun v _ => hd v) hU

end GlobalTheory.HoweR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHalfIdem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatAut

open GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.SplitScalar

variable {D : D7}

def IsHalfIdem (D : D7) (ε : AE D) : Prop :=
  ε * ε = ε ∧ ε * cA D ε = 0 ∧ infPart D ε = 0 ∧
    (∀ e, IsSplitIdem D e → (ε * e = e ∧ ε * cA D e = 0) ∨ (ε * e = 0 ∧ ε * cA D e = cA D e)) ∧
    ∀ v η, NonSplitAt D v η → algebraMap (AF D.host.F) (AE D) η * ε = 0

theorem exists_isHalfIdem (D : D7) : ∃ ε, IsHalfIdem D ε := GlobalTheory.T.exists_splitPlaces_selecting_adelicIdempotent D

theorem finRat_eq (S T : HSp D) (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    finRat S T x = (1 - realIdem D) • (ratW T S x : WO S T) := by
  funext i j
  refine adele_ext ?_ ?_
  · exact (congrFun (congrFun (finRat_inf S T x) i) j).trans (congrFun (congrFun (fin_smul_fin (ratW T S x)) i) j).symm
  · show finPart D (ratW T S x i j) = finPart D ((1 - realIdem D) * ratW T S x i j)
    rw [RingHom.map_mul, RingHom.map_sub, finPart_realIdem, RingHom.map_one, sub_zero, one_mul]

theorem finRat_smul (S T : HSp D) (c : D.host.E) (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    finRat S T (c • x) = incA D c • finRat S T x := by
  rw [finRat_eq, finRat_eq, smul_comm]
  congr 1
  funext i j
  exact (incA D).map_mul c (x i j)

def latQ (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) :
    Submodule (𝓞 D.host.E) (Matrix (Fin T.rank) (Fin S.rank) D.host.E) where
  carrier := {x | finRat S T x ∈ latO S T LS LT fun _ => True}
  add_mem' {x y} hx hy := by
    show finRat S T (x + y) ∈ latO S T LS LT fun _ => True
    rw [map_add]
    exact add_mem hx hy
  zero_mem' := by
    show finRat S T 0 ∈ latO S T LS LT fun _ => True
    rw [map_zero]
    exact zero_mem _
  smul_mem' r x hx := by
    show finRat S T ((r : D.host.E) • x) ∈ latO S T LS LT fun _ => True
    rw [finRat_smul]
    exact GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ _ (finPart_intA r) _ hx

theorem mem_latQ {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {x : Matrix (Fin T.rank) (Fin S.rank) D.host.E} :
    x ∈ latQ S T LS LT ↔ finRat S T x ∈ latO S T LS LT fun _ => True := Iff.rfl

def gamQ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : ℂ :=
  ψ (symplO S T (finRat S T x) (finRat S T y))

open Classical in

def chiLat (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (w : 𝓞 D.host.E) (x : WO S T) : ℂ :=
  if (1 - realIdem D) • x ∈ latO S T LS LT (fun _ => True) then
    ψ (symplOH S T (intA D w • (1 - realIdem D) • x) ((1 - realIdem D) • x)) else 0

def serO (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (w : 𝓞 D.host.E) (a : RW T S) : WO S T → ℂ :=
  GlobalTheory.HeisenbergGaussianSeries.series (G := WO S T) (piW θ T S) (iotaW σ T S) (fun x y => ψ (symplOH S T x y))
    (omO S T) (jO S T sS sT) (ratL T S) (chiLat ψ S T LS LT w) a

def actR (S T : HSp D) (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (v : RW T S) : RW T S :=
  fun τ => (b τ * Matrix.of (v τ) * a τ : Matrix (Fin T.rank) (Fin S.rank) ℂ)

def gaussR (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (v : RW T S) : ℂ :=
  Complex.exp (-(Real.pi * Complex.I) * (omO S T (actR S T a b v) v : ℝ)) *
    Complex.exp (-(Real.pi / 2 : ℂ) * (omO S T (actR S T a b v - v) (jO S T sS sT (actR S T a b v - v)) : ℝ))

def sandw {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K) :
    Module.End K (Matrix (Fin m) (Fin n) K) where
  toFun x := b * x * a
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

theorem sandw_apply {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K)
    (x : Matrix (Fin m) (Fin n) K) : sandw b a x = b * x * a := rfl

theorem toMatrix_sandw {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K) :
    LinearMap.toMatrix (Matrix.stdBasis K (Fin m) (Fin n)) (Matrix.stdBasis K (Fin m) (Fin n)) (sandw b a) = b ⊗ₖ aᵀ := by
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single, sandw_apply]
  have : ∀ x : Matrix (Fin m) (Fin n) K, (Matrix.stdBasis K (Fin m) (Fin n)).repr x (i, j) = x i j := fun x => by
    simp [Matrix.stdBasis]
  rw [this]
  simp [Matrix.mul_apply, Matrix.single, ite_and]

theorem det_sandw {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K) :
    LinearMap.det (sandw b a) = (b ⊗ₖ aᵀ).det := by
  rw [← toMatrix_sandw, LinearMap.det_toMatrix]

theorem det_sandw_sub_one {K : Type} [CommRing K] {m n : ℕ} (b : Matrix (Fin m) (Fin m) K) (a : Matrix (Fin n) (Fin n) K) :
    LinearMap.det (sandw b a - 1) = (b ⊗ₖ aᵀ - 1).det := by
  rw [← toMatrix_sandw, ← LinearMap.det_toMatrix (Matrix.stdBasis K (Fin m) (Fin n)), map_sub, LinearMap.toMatrix_one]

end GlobalTheory.RatAut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicDualPartnerSelfDualHermitianLatti
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.TraceCorrection

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

theorem form_add_left (x x' y : Fin n → E) : form σ J (x + x') y = form σ J x y + form σ J x' y := by
  simp [form, add_dotProduct]

theorem form_add_right (x y y' : Fin n → E) : form σ J x (y + y') = form σ J x y + form σ J x y' := by
  have h : (fun i => σ ((y + y') i)) = (fun i => σ (y i)) + fun i => σ (y' i) := by
    ext i; simp
  simp only [form, h, Matrix.mulVec_add, dotProduct_add]

theorem form_smul_left (c : E) (x y : Fin n → E) : form σ J (c • x) y = c * form σ J x y := by
  simp [form, smul_dotProduct]

theorem form_smul_right (c : E) (x y : Fin n → E) : form σ J x (c • y) = σ c * form σ J x y := by
  have h : (fun i => σ ((c • y) i)) = σ c • fun i => σ (y i) := by
    ext i; simp
  simp only [form, h, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_symm (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    σ (form σ J x y) = form σ J y x := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem exists_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)),
    (∀ i j, σ (J j i) = J i j) → (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (form σ J y x)) →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ x y₀ : Fin n → E, form σ J x x = 0 → form σ J y₀ x = 1 →
    (∀ z ∈ L, form σ J z x • y₀ ∈ L) →
    ∃ y : Fin n → E, form σ J y y = 0 ∧ form σ J x y = 1 ∧ ∀ z ∈ L, form σ J z y • x ∈ L ∧ form σ J z x • y ∈ L := by
  intro F E _ _ _ _ _ σ hσ n J L hJ hL θ hθ x y₀ hxx hy₀x hL0
  have hsa : σ (form σ J y₀ y₀) = form σ J y₀ y₀ := form_symm σ J hσ hJ y₀ y₀
  have hxw : ∀ w, form σ J x w = σ (form σ J w x) := fun w => (form_symm σ J hσ hJ w x).symm
  have hxy₀ : form σ J x y₀ = 1 := by rw [hxw, hy₀x, map_one]
  have hsθ : σ (θ : E) = 1 - θ := by linear_combination hθ
  have hθi : IsIntegral ℤ (θ : E) := θ.isIntegral_coe
  have hA : ∀ z ∈ L, ∀ w ∈ L,
      IsIntegral ℤ (form σ J y₀ y₀ * form σ J z x * σ (form σ J w x)) := by
    intro z hz w hw
    have h := (hL _).1 (hL0 z hz) _ (hL0 w hw)
    rw [form_smul_left, form_smul_right] at h
    have k : form σ J z x * (σ (form σ J w x) * form σ J y₀ y₀) =
        form σ J y₀ y₀ * form σ J z x * σ (form σ J w x) := by ring
    rw [← k]; exact h
  refine ⟨y₀ + (-((θ : E) * form σ J y₀ y₀)) • x, ?_, ?_, ?_⟩
  · simp only [form_add_left, form_add_right, form_smul_left, form_smul_right, hxx, hxy₀, hy₀x,
      map_neg, map_mul, hsθ, hsa]
    ring
  · simp only [form_add_right, form_smul_right, hxx, hxy₀]
    ring
  intro z hz
  constructor
  · have e : form σ J z (y₀ + (-((θ : E) * form σ J y₀ y₀)) • x) • x =
        form σ J z y₀ • x + (σ (-((θ : E) * form σ J y₀ y₀)) * form σ J z x) • x := by
      rw [form_add_right, form_smul_right, add_smul]
    rw [e]
    refine L.add_mem ((hL _).2 fun w hw => ?_) ((hL _).2 fun w hw => ?_)
    · have h := (hL z).1 hz _ (hL0 w hw)
      rw [form_smul_right] at h
      rw [form_smul_left, hxw, mul_comm]
      exact h
    · rw [form_smul_left, hxw]
      have h := (hA z hz w hw).neg.add (hθi.mul (hA z hz w hw))
      have k : σ (-((θ : E) * form σ J y₀ y₀)) * form σ J z x * σ (form σ J w x) =
          -(form σ J y₀ y₀ * form σ J z x * σ (form σ J w x)) +
            (θ : E) * (form σ J y₀ y₀ * form σ J z x * σ (form σ J w x)) := by
        rw [map_neg, map_mul, hsθ, hsa]; ring
      rw [k]; exact h
  · have e : form σ J z x • (y₀ + (-((θ : E) * form σ J y₀ y₀)) • x) =
        form σ J z x • y₀ + (form σ J z x * (-((θ : E) * form σ J y₀ y₀))) • x := by
      rw [smul_add, mul_smul]
    rw [e]
    refine L.add_mem (hL0 z hz) ((hL _).2 fun w hw => ?_)
    rw [form_smul_left, hxw]
    have h := (hθi.mul (hA z hz w hw)).neg
    have k : form σ J z x * (-((θ : E) * form σ J y₀ y₀)) * σ (form σ J w x) =
        -((θ : E) * (form σ J y₀ y₀ * form σ J z x * σ (form σ J w x))) := by ring
    rw [k]; exact h

end GlobalTheory.TraceCorrection
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicPlaces
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.PlaceIso

theorem denseRange_algebraMap_completion : ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), DenseRange (algebraMap F w.Completion) := by
  intro F _ _ w y
  have h := InfinitePlace.Completion.denseRange_coe w y
  convert h using 2
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(WithAbs.equiv w.1).symm x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨WithAbs.equiv w.1 x, rfl⟩

theorem exists_isotropic_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∃ (S₁' : Finset (InfinitePlace F)) (S₂' : Finset (HeightOneSpectrum (𝓞 F))) (ε' : AF F), S₁' ⊆ S₁ ∧ S₂' ⊆ S₂ ∧ (S₁'.Nonempty ∨ S₂'.Nonempty) ∧ IsPlacesIdem S₁' S₂' ε' ∧ ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0) := by
  intro F E _ _ _ _ _ σ hσ M J hM hJ S₁ S₂ ε hε hnc
  classical
  have key : (∃ w ∈ S₁, ∃ u : Fin M → w.Completion ⊗[F] E, u ≠ 0 ∧ hR w.Completion σ J u u = 0) ∨
      (∃ v ∈ S₂, ∃ u : Fin M → Fv F v ⊗[F] E, u ≠ 0 ∧ hR (Fv F v) σ J u u = 0) := by
    by_contra hno
    push_neg at hno
    apply hnc
    apply GlobalTheory.T.isCompact_specialUnitary_supportedAtPlaces F E σ hσ M J hJ S₁ S₂ ε hε
    · intro w hw
      letI := GroundTheory.Automorphic.completionNontriviallyNormedField (K := F) w
      exact GlobalTheory.T.exists_compact_set_unitary_hermitian_real F E σ hσ w.Completion M J hJ (fun u hu => by
        by_contra h
        exact hno.1 w hw u h hu)
    · intro v hv
      letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
      haveI := Formalism.BasicNotions.Examples₂.LocF.proper v
      exact GlobalTheory.T.exists_compact_set_unitary_hermitian_real F E σ hσ (Fv F v) M J hJ (fun u hu => by
        by_contra h
        exact hno.2 v hv u h hu)
  rcases key with ⟨w, hw, u, hu0, hu⟩ | ⟨v, hv, u, hu0, hu⟩
  · obtain ⟨ε', hε'⟩ := GlobalTheory.Published.StrongApprox.exists_isPlacesIdem (F := F) {w} ∅
    refine ⟨{w}, ∅, ε', Finset.singleton_subset_iff.2 hw, Finset.empty_subset _,
      Or.inl (Finset.singleton_nonempty w), hε', ?_⟩
    intro x y hx hy
    letI := GroundTheory.Automorphic.completionNontriviallyNormedField (K := F) w
    obtain ⟨z, hz, ⟨h1, ht1⟩, ⟨h2, ht2⟩⟩ :=
      GlobalTheory.T.exists_rational_vector_isotropic_nondegenerate_planes_at_place F E σ hσ w.Completion (denseRange_algebraMap_completion F w) M J hM hJ ⟨u, hu0, hu⟩ x y hx hy
    exact ⟨z, hz, ⟨h1, GlobalTheory.T.exists_norm_solution_adelic_from_archimedean F E σ w ε' hε' _ ht1⟩, ⟨h2, GlobalTheory.T.exists_norm_solution_adelic_from_archimedean F E σ w ε' hε' _ ht2⟩⟩
  · obtain ⟨ε', hε'⟩ := GlobalTheory.Published.StrongApprox.exists_isPlacesIdem (F := F) ∅ {v}
    refine ⟨∅, {v}, ε', Finset.empty_subset _, Finset.singleton_subset_iff.2 hv,
      Or.inr (Finset.singleton_nonempty v), hε', ?_⟩
    intro x y hx hy
    letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
    obtain ⟨z, hz, ⟨h1, ht1⟩, ⟨h2, ht2⟩⟩ :=
      GlobalTheory.T.exists_rational_vector_isotropic_nondegenerate_planes_at_place F E σ hσ (Fv F v) (HeightOneSpectrum.denseRange_algebraMap F v) M J hM hJ ⟨u, hu0, hu⟩ x y hx hy
    exact ⟨z, hz, ⟨h1, GlobalTheory.T.idempotent_adelic_norm_eq_of_local_norm_eq F E σ v ε' hε' _ ht1⟩, ⟨h2, GlobalTheory.T.idempotent_adelic_norm_eq_of_local_norm_eq F E σ v ε' hε' _ ht2⟩⟩
end GlobalTheory.PlaceIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicVectorHermitianRankGeThreeIndefin
section
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.HermIso

theorem posIndex_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) :
    GlobalTheory.Inertia.posIndex M = r := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let D : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ :=
    Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))
  have hD : Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1) = D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [D, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have hA' : A'ᵀ * M * A'.map (starRingEnd ℂ) = D.submatrix e.symm e.symm := by
    rw [← hD, ← hA]
    ext i j
    simp [A', Matrix.mul_apply, Matrix.transpose_apply]
  have hdet : A'.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hA'
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, Matrix.det_submatrix_equiv_self,
      Matrix.det_diagonal] at h1
    simp [Fintype.prod_sum_type] at h1
    exact pow_ne_zero s (by norm_num) h1.symm
  rw [← GlobalTheory.Inertia.posIndex_congr M hdet, hA', GlobalTheory.Inertia.posIndex_submatrix_equiv,
    GlobalTheory.Inertia.posIndex_diagonal]
  rw [Finset.card_filter, Fintype.sum_sum_type]
  simp

theorem exists_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ (n : ℕ) (Y : Spc F E n) (r s : ℕ), 3 ≤ n → 1 ≤ r → 1 ≤ s →
    Y.IsHerm σ B r s → ∃ x : Fin n → E, x ≠ 0 ∧ form σ Y.J x x = 0 := by
  intro F E _ _ _ _ _ σ B hB n Y r s hn hr hs hY
  obtain ⟨-, hEC, h2, hconj⟩ := hB.cm
  obtain ⟨w0⟩ : Nonempty (InfinitePlace E) := inferInstance
  have invol : ∀ x, σ (σ x) = x := fun x =>
    w0.embedding.injective (by rw [hconj, hconj, star_star])
  let σe : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext invol) (AlgHom.ext invol)
  have hne : σe ≠ 1 := by
    intro h
    have hid : ∀ x, σ x = x := fun x => by simpa [σe] using DFunLike.congr_fun h x
    have hre : ComplexEmbedding.IsReal w0.embedding :=
      ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
        rw [ComplexEmbedding.conjugate_coe_eq]
        have := hconj w0.embedding x
        rw [hid] at this
        exact this.symm)
    exact InfinitePlace.not_isReal_iff_isComplex.2 (hEC.isComplex w0) (InfinitePlace.isReal_iff.2 hre)
  haveI : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  obtain ⟨hc, hF, θ, hθ0, hθ⟩ := GlobalTheory.HermGlobal.involutive_and_fixed hne
  obtain ⟨P, g, hP, hPg, hgf, hg0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E))
    two_ne_zero (fun t => invol t) (G := Y.J) (fun a b => hY.herm b a)
  have hgf' : ∀ i, σ (g i) = g i := fun i => hgf i
  have key : ∀ y : Fin n → E,
      form σ Y.J (P *ᵥ y) (P *ᵥ y) = y ⬝ᵥ Matrix.diagonal g *ᵥ (fun i => σ (y i)) := by
    intro y
    have h1 : (fun i => σ ((P *ᵥ y) i)) = (P.map (σ : E →+* E)) *ᵥ (fun i => σ (y i)) := by
      funext i
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [form, h1, ← hPg]
    simp only [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec]
    rw [← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, Matrix.mul_assoc]
  by_cases hz : ∃ i, g i = 0
  · obtain ⟨i, hi⟩ := hz
    refine ⟨P *ᵥ Pi.single i 1, fun h => ?_, ?_⟩
    · have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) i
      simp at this
    · rw [key]
      simp [Matrix.mulVec_diagonal, dotProduct, Pi.single_apply, hi]
  push_neg at hz
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hsg : ∀ τ : E →+* ℂ, (∀ x, τ (σe x) = conj (τ x)) →
      ∃ i : Fin m, (0 < (τ (g i.succ)).re ↔ 0 < (τ (-g 0)).re) := by
    intro τ _
    have hre : ComplexEmbedding.IsReal (τ.comp (algebraMap F E)) :=
      ComplexEmbedding.isReal_iff.2 (RingHom.ext fun c => by
        rw [ComplexEmbedding.conjugate_coe_eq]
        have := hconj τ (algebraMap F E c)
        rw [AlgHom.commutes] at this
        exact this.symm)
    have hw : (InfinitePlace.mk (τ.comp (algebraMap F E))).embedding = τ.comp (algebraMap F E) :=
      InfinitePlace.embedding_mk_eq_of_isReal hre
    set w := InfinitePlace.mk (τ.comp (algebraMap F E))
    set τ' := (B.emb w).1
    have hτ' : ∀ c : F, τ' (algebraMap F E c) = τ (algebraMap F E c) := fun c => by
      have := congrArg (fun f => f c) ((B.emb w).2.trans hw)
      simpa using this
    have hgτ : ∀ k, τ' (g k) = τ (g k) := fun k => by
      obtain ⟨c, hc'⟩ := (hF (g k)).1 (hgf' k)
      rw [← hc', hτ']
    have hcong : (Matrix.diagonal g).map τ' =
        (P.map τ')ᵀ * Y.J.map τ' * (P.map τ').map (starRingEnd ℂ) := by
      rw [← hPg, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
      congr 1
      ext a b
      simp [hconj]
    have hPd : (P.map τ').det ≠ 0 := by
      rw [show (P.map τ').det = τ' P.det from (RingHom.map_det τ' P).symm]
      exact (map_ne_zero τ').2 hP
    have hcount : (Finset.univ.filter fun k => 0 < (τ (g k)).re).card = r := by
      have := GlobalTheory.Inertia.posIndex_congr (Y.J.map τ') hPd
      rw [← hcong, posIndex_of_hasSig (hY.sig w), Matrix.diagonal_map (map_zero _),
        GlobalTheory.Inertia.posIndex_diagonal] at this
      simpa [hgτ] using this
    have hrn : r < m + 1 := by have := (hY.sig w).1; omega
    have him : (τ (g 0)).im = 0 := by
      have h := hconj τ (g 0)
      rw [hgf' 0] at h
      exact Complex.conj_eq_iff_im.1 h.symm
    have hne0 : τ (g 0) ≠ 0 := (map_ne_zero τ).2 (hz 0)
    by_cases hp : 0 < (τ (g 0)).re
    · obtain ⟨k, hk⟩ : ∃ k, ¬ 0 < (τ (g k)).re := by
        by_contra hall
        push_neg at hall
        have h' : (Finset.univ.filter fun k => 0 < (τ (g k)).re) = Finset.univ :=
          Finset.filter_true_of_mem fun k _ => hall k
        rw [h', Finset.card_univ, Fintype.card_fin] at hcount
        omega
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 (show k ≠ 0 by rintro rfl; exact hk hp)
      refine ⟨i, iff_of_false hk ?_⟩
      simp only [map_neg, Complex.neg_re]
      linarith
    · have hneg : (τ (g 0)).re < 0 := by
        rcases lt_or_eq_of_le (not_lt.1 hp) with h | h
        · exact h
        · exact absurd (Complex.ext (by simpa using h) (by simpa using him)) hne0
      obtain ⟨k, hk⟩ : ∃ k, 0 < (τ (g k)).re := by
        by_contra hall
        push_neg at hall
        have h' : (Finset.univ.filter fun k => 0 < (τ (g k)).re) = ∅ :=
          Finset.filter_false_of_mem fun k _ => not_lt.2 (hall k)
        rw [h', Finset.card_empty] at hcount
        omega
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 (show k ≠ 0 by rintro rfl; exact hp hk)
      refine ⟨i, iff_of_true hk ?_⟩
      simp only [map_neg, Complex.neg_re]
      linarith
  obtain ⟨z, hz'⟩ := GlobalTheory.HermGlobal.exists_represent hc hF hθ0 hθ (r := m) (by omega)
    (g := fun i => g i.succ) (fun i => hgf' _) (fun i => hz _) (b := -g 0)
    (by simp [σe, hgf']) (neg_ne_zero.2 (hz 0)) hsg
  refine ⟨P *ᵥ Fin.cons 1 z, fun h => ?_, ?_⟩
  · have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) 0
    simp at this
  · rw [key]
    simp only [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      map_one, one_mul, mul_one] at hz' ⊢
    simp only [σe, Function.comp_apply, RingHom.coe_coe, AlgEquiv.ofAlgHom_apply] at hz'
    linear_combination hz'

end GlobalTheory.HermIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroConjNegOfCmExtension
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.CMTraceZero

theorem exists_ne_zero_conj_neg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ ξ₀ : E, ξ₀ ≠ 0 ∧ σ ξ₀ = -ξ₀ := by
  intro F E _ _ _ _ _ σ B hB
  obtain ⟨_, hc, _, hτ⟩ := hB.cm
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hinv : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hτ, hτ, star_star])
  have hne : ∃ x, σ x ≠ x := by
    by_contra hall
    push_neg at hall
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have hw := hc.isComplex w
    rw [InfinitePlace.isComplex_iff] at hw
    apply hw
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have := hτ w.embedding x
    rw [hall x] at this
    simpa using this.symm
  obtain ⟨x, hx⟩ := hne
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), ?_⟩
  rw [map_sub, hinv, neg_sub]

end GlobalTheory.CMTraceZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulVeryAmpleSubIsEffectivePicClassStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nsmul_veryAmple_sub_isEffectivePicClass : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [Nonempty Y] (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y) (hH : H.IsLB) (hM : M.IsLB), GlobalTheory.AbLaw.VeryAmpleBy f H s → ∃ c : ℕ, GlobalTheory.EffBound.Eff (c • GlobalTheory.CechPic.cls H hH - GlobalTheory.CechPic.cls M hM) := by
  first | exact @GlobalTheory.EffBound.exists_nsmul_sub_eff | exact GlobalTheory.EffBound.exists_nsmul_sub_eff | (intros; apply GlobalTheory.EffBound.exists_nsmul_sub_eff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceHalfHeisenbergInvariantFormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_split_place_half_heisenberg_invariant_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (e : AE D), IsSplitIdem D e → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ ∃ f, IsThetaFunO ψ S T f ∧ ℓ f ≠ 0 := by
  first | exact @GlobalTheory.HalfCoinv.exists_invariant_form | exact GlobalTheory.HalfCoinv.exists_invariant_form | (intros; apply GlobalTheory.HalfCoinv.exists_invariant_form <;> assumption)
end

