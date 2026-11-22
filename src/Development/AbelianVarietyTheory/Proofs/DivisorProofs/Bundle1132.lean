import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0925
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormUnitCommutation
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory

theorem twisted_norm_local_step : ∀ {A K : Type} [Ring A] [CommRing K] [Algebra K A] (σ : A →+* Aᵐᵒᵖ), (∀ x, (σ (σ x).unop).unop = x) →
    ∀ (β Y k z m : Aˣ) (a : A) (lam s : Kˣ), (σ (β : A)).unop = β →
    (Y : A) * β * (σ (Y : A)).unop = algebraMap K A s * β → Commute a Y →
    (k : A) * (a * β) * (σ (k : A)).unop = algebraMap K A lam → k⁻¹ = z * m → Commute (z : A) Y →
    (∀ m' : Aˣ, (m' : A) = m * (σ (m : A)).unop * ((β⁻¹ : Aˣ) : A) → Commute (m' : A) Y →
      (β : A) * (σ (m' : A)).unop * ((β⁻¹ : Aˣ) : A) = m' →
      ∃ v : Aˣ, Commute (v : A) Y ∧ (m' : A) = v * ((β : A) * (σ (v : A)).unop * ((β⁻¹ : Aˣ) : A))) →
    ∃ z' : Aˣ, Commute (z' : A) Y ∧ a = algebraMap K A lam * ((z' : A) * β * (σ (z' : A)).unop * ((β⁻¹ : Aˣ) : A)) := by
  intro A K _ _ _ σ hσ β Y k z m a lam s hβ hY haY hk hkz hzY H
  have shmul : ∀ x y : A, (σ (x * y)).unop = (σ y).unop * (σ x).unop := fun x y => by
    rw [map_mul, MulOpposite.unop_mul]
  have shinv : ∀ u : Aˣ, (σ ((u⁻¹ : Aˣ) : A)).unop * (σ (u : A)).unop = 1 := fun u => by
    rw [← shmul, Units.mul_inv, map_one, MulOpposite.unop_one]
  have shinv' : ∀ u : Aˣ, (σ (u : A)).unop * (σ ((u⁻¹ : Aˣ) : A)).unop = 1 := fun u => by
    rw [← shmul, Units.inv_mul, map_one, MulOpposite.unop_one]
  have shc : ∀ (u : Aˣ) (x : A), (σ (u : A)).unop * ((σ ((u⁻¹ : Aˣ) : A)).unop * x) = x := by
    intro u x; rw [← mul_assoc, shinv', one_mul]

  have hτY : (β : A) * (σ (Y : A)).unop * ((β⁻¹ : Aˣ) : A) = algebraMap K A s * ((Y⁻¹ : Aˣ) : A) := by
    have h := congrArg (fun x => ((Y⁻¹ : Aˣ) : A) * x * ((β⁻¹ : Aˣ) : A)) hY
    simp only [mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, mul_one] at h
    rw [mul_assoc, h]
    exact (Algebra.commutes _ _).symm
  have hτ : ∀ w : A, Commute w Y → Commute ((β : A) * (σ w).unop * ((β⁻¹ : Aˣ) : A)) Y := by
    intro w hw
    have hsh : Commute (σ w).unop (σ (Y : A)).unop := by
      show _ = _
      rw [← shmul, ← shmul, hw.eq]
    have hc : Commute ((β : A) * (σ w).unop * ((β⁻¹ : Aˣ) : A))
        ((β : A) * (σ (Y : A)).unop * ((β⁻¹ : Aˣ) : A)) := by
      show _ = _
      simp only [mul_assoc, Units.inv_mul_cancel_left]
      rw [← mul_assoc (σ w).unop, hsh.eq, mul_assoc]
    rw [hτY] at hc
    have h2 := (Algebra.commute_algebraMap_right ((s⁻¹ : Kˣ) : K) _).mul_right hc
    rw [← mul_assoc (algebraMap K A ((s⁻¹ : Kˣ) : K)), ← map_mul, Units.inv_mul, map_one,
      one_mul] at h2
    exact Commute.units_inv_right_iff.mp h2

  have e : a * (β : A) = ((k⁻¹ : Aˣ) : A) * ((k : A) * (a * β) * (σ (k : A)).unop) *
      (σ ((k⁻¹ : Aˣ) : A)).unop := by
    simp only [mul_assoc, shinv', shc, mul_one, Units.inv_mul_cancel_left]
  rw [hk, ← Algebra.commutes (lam : K), hkz, Units.val_mul, shmul] at e
  have ha : a = algebraMap K A lam * ((z : A) * ((m : A) * (σ (m : A)).unop) * (σ (z : A)).unop *
      ((β⁻¹ : Aˣ) : A)) := by
    calc a = a * β * ((β⁻¹ : Aˣ) : A) := by rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [e]; simp only [mul_assoc]

  have hbi : (σ ((β⁻¹ : Aˣ) : A)).unop = ((β⁻¹ : Aˣ) : A) := by
    have h := shinv β
    rw [hβ] at h
    calc (σ ((β⁻¹ : Aˣ) : A)).unop = (σ ((β⁻¹ : Aˣ) : A)).unop * β * ((β⁻¹ : Aˣ) : A) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h, one_mul]
  let mu : Aˣ := ⟨(σ (m : A)).unop, (σ ((m⁻¹ : Aˣ) : A)).unop, shinv' m, shinv m⟩
  let m' : Aˣ := m * mu * β⁻¹
  have hm' : (m' : A) = m * (σ (m : A)).unop * ((β⁻¹ : Aˣ) : A) := rfl
  have hm'c : (m' : A) = ((z⁻¹ : Aˣ) : A) * (algebraMap K A ((lam⁻¹ : Kˣ) : K) * a) *
      ((β : A) * (σ ((z⁻¹ : Aˣ) : A)).unop * ((β⁻¹ : Aˣ) : A)) := by
    rw [hm', ha, ← mul_assoc (algebraMap K A ((lam⁻¹ : Kˣ) : K)), ← map_mul, Units.inv_mul,
      map_one, one_mul]
    simp only [mul_assoc, Units.inv_mul_cancel_left, shc]
  have hmY : Commute (m' : A) Y := by
    rw [hm'c]
    exact ((hzY.units_inv_left).mul_left
      ((Algebra.commute_algebraMap_left _ _).mul_left haY)).mul_left (hτ _ hzY.units_inv_left)
  have hmτ : (β : A) * (σ (m' : A)).unop * ((β⁻¹ : Aˣ) : A) = m' := by
    rw [hm', shmul, shmul, hσ, hbi]
    simp only [mul_assoc, Units.mul_inv_cancel_left]
  obtain ⟨v, hvY, hv⟩ := H m' hm' hmY hmτ
  have h3 : (m : A) * (σ (m : A)).unop * ((β⁻¹ : Aˣ) : A) =
      v * β * (σ (v : A)).unop * ((β⁻¹ : Aˣ) : A) := by
    rw [← hm', hv]; simp only [mul_assoc]
  have hmm := (Units.mul_left_inj β⁻¹).mp h3
  refine ⟨z * v, by rw [Units.val_mul]; exact hzY.mul_left hvY, ?_⟩
  rw [Units.val_mul, shmul, ha, hmm]
  simp only [mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFormOrthogonalComplement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult

theorem orthogonal_kstable_compl : ∀ (R S : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ), IsUnitary actW B →
    ∀ U : Submodule ℂ W, KStable actW U → KStable actW (U.orthogonalBilin B) ∧ U ⊔ U.orthogonalBilin B = ⊤ := by
  intro R S W _ _ _ actW B hB U hU
  obtain ⟨_, hpos, hadj⟩ := hB
  constructor
  · intro X hX x hx
    refine GlobalTheory.TensorHW.kc_ind actW (U.orthogonalBilin B) x (fun a b hab => ?_) hX
    rw [Submodule.mem_orthogonalBilin_iff] at hx ⊢
    intro n hn
    have hba : sameBlock b a := by
      cases a <;> cases b <;> simp_all [sameBlock]
    have h := hadj b a hba n x
    show B n (actW (Eab a b) x) = 0
    rw [← h]
    exact hx _ (hU _ (GlobalTheory.TensorHW.isKC_Eab hba) n hn)
  · have hinf : U ⊓ U.orthogonalBilin B = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨hxU, hxo⟩ := Submodule.mem_inf.mp hx
      rw [Submodule.mem_orthogonalBilin_iff] at hxo
      have h0 : B x x = 0 := hxo x hxU
      rw [Submodule.mem_bot]
      by_contra hne
      have h := hpos x hne
      rw [h0] at h
      simp at h
    let b := Module.finBasis ℂ U
    let ψ : W →ₗ[ℂ] (Fin (Module.finrank ℂ U) → ℂ) := LinearMap.pi (fun i => B (b i : W))
    have hker : LinearMap.ker ψ ≤ U.orthogonalBilin B := by
      intro x hx
      rw [LinearMap.mem_ker] at hx
      rw [Submodule.mem_orthogonalBilin_iff]
      intro n hn
      have hf : (B.flip x).comp U.subtype = 0 := by
        refine b.ext (fun i => ?_)
        have h := congrFun hx i
        simpa [ψ] using h
      have h := LinearMap.congr_fun hf ⟨n, hn⟩
      simpa using h
    have h1 := LinearMap.finrank_range_add_finrank_ker ψ
    have h2 : Module.finrank ℂ (LinearMap.range ψ) ≤ Module.finrank ℂ U := by
      have h := Submodule.finrank_le (LinearMap.range ψ)
      simpa using h
    have h3 := Submodule.finrank_mono hker
    have h4 := Submodule.finrank_sup_add_finrank_inf_eq U (U.orthogonalBilin B)
    rw [hinf, finrank_bot] at h4
    apply Submodule.eq_top_of_finrank_eq
    apply le_antisymm (Submodule.finrank_le _)
    omega

end GlobalTheory.SteepMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversallyClosedOpenContainingFibreContainsNear
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem spMap_base_mem_basicOpen {R T : Type} [CommRing R] [CommRing T] (χ : R →+* T) (a : R)
    (ha : IsUnit (χ a)) (t : Sp T) : (spMap χ).base t ∈ (PrimeSpectrum.basicOpen a : (Sp R).Opens) := by
  change a ∉ (PrimeSpectrum.comap χ t).asIdeal
  intro h
  exact t.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h ha)

theorem tube_of_universallyClosed : ∀ (R k : Type) [CommRing R] [Field k] (φ : R →+* k) (X X' : Scheme.{0})
    (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) [UniversallyClosed f] (W : X.Opens),
    IsPullback π f' f (spMap φ) → π ⁻¹ᵁ W = ⊤ → ∃ a : R, φ a ≠ 0 ∧ ∀ (T : Type) [CommRing T] (χ : R →+* T),
    IsUnit (χ a) → ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp T) (ρ : Z ⟶ X), IsPullback ρ g f (spMap χ) → ρ ⁻¹ᵁ W = ⊤ := by
  intro R k _ _ φ X X' f f' π _ W H hW
  have hc : IsClosed (f.base '' (W : Set X)ᶜ) := f.isClosedMap _ W.isOpen.isClosed_compl
  let t : Sp k := ⟨⊥, Ideal.isPrime_bot⟩
  have hx : (spMap φ).base t ∈ (f.base '' (W : Set X)ᶜ)ᶜ := by
    rintro ⟨x, hx, e⟩
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback H x t e
    exact hx (hW.ge (Set.mem_univ z))
  obtain ⟨_, ⟨a, rfl⟩, ha, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx hc.isOpen_compl
  refine ⟨a, ?_, ?_⟩
  · intro h0
    apply ha
    change φ a ∈ (⊥ : Ideal k)
    exact h0
  · intro T _ χ hχ Z g ρ H'
    refine top_le_iff.1 fun z _ => ?_
    by_contra hz
    have hm := spMap_base_mem_basicOpen χ a hχ (g.base z)
    have e : f.base (ρ.base z) = (spMap χ).base (g.base z) := by
      have := congrArg (fun h : Z ⟶ Sp R => h.base z) H'.w
      simpa using this
    exact hle (e ▸ hm : f.base (ρ.base z) ∈ _) ⟨ρ.base z, hz, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterAtUniformizerStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_character_at_uniformizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : Chr F E) (v : Pl F) (t : E →ₐ[F] Fv F v), UnrAt χ (splitPrime t) → chrW χ t (unifAt v) = val χ (splitPrime t) := by
  first | exact @GlobalTheory.ChrWUnif.chrW_unifAt | exact GlobalTheory.ChrWUnif.chrW_unifAt | (intros; apply GlobalTheory.ChrWUnif.chrW_unifAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtensionProductDecompositionStatement
section
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKRes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_extension_product_decomposition : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (f r : ℕ), qK p K = p ^ f → 0 < r → ∃ (e : KQ p K r ≃+* (Fin (Nat.gcd f r) → Kn p K (r / Nat.gcd f r))) (τ : Kn p K (r / Nat.gcd f r) ≃+* Kn p K (r / Nat.gcd f r)), (∀ x, (τ x = x ↔ (x : PadicAlgCl p) ∈ K)) ∧ (∀ x, (⇑τ)^[r / Nat.gcd f r] x = x) ∧ (∀ (a : K) (i : Fin (Nat.gcd f r)), ((e (inclK p K r a) i : Kn p K (r / Nat.gcd f r)) : PadicAlgCl p) = a) ∧ (∀ (x : KQ p K r) (i : Fin (Nat.gcd f r)) (h : i.val + 1 < Nat.gcd f r), e (sigKQ p K r x) i = e x ⟨i.val + 1, h⟩) ∧ (∀ (x : KQ p K r) (i : Fin (Nat.gcd f r)), i.val + 1 = Nat.gcd f r → ∀ (i0 : Fin (Nat.gcd f r)), i0.val = 0 → e (sigKQ p K r x) i = τ (e x i0)) ∧ (∀ x : KQ p K r, x ∈ intKQ p K r ↔ ∀ i, e x i ∈ GlobalTheory.LKLoc.intR p K (r / Nat.gcd f r)) := by
  first | exact @GlobalTheory.LKRes.ResSplit.kq_split | exact GlobalTheory.LKRes.ResSplit.kq_split | (intros; apply GlobalTheory.LKRes.ResSplit.kq_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecOfEqSumHeis
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DatumFourierOnCmp

open GlobalTheory.DatumFourier

set_option maxHeartbeats 1600000 in

theorem vecOf_eq_sum_heis : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), VStd D i → ∀ (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)), LatEmb (Wc D i) ι → LatIsom (Wc D i) Dw.EF ι → ∃ δ : ℤˣ, ∀ (χ : (AE D)ˣ →* Circle) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (Ω : GlobalTheory.OnCmp.DatFn D i) (ω : GlobalTheory.OnTies.WeilRep D i) (φv : WO (Vc D i) (Wc D i) → ℂ), GlobalTheory.OnCmp.IsWeilTw R i χ ω → Formalism.IndefR.Lev.IsTwistPlaces D.host.g Q → GlobalTheory.OnCmp.ReadsOnly (R.Pg ∪ Q) Ω → GlobalTheory.OnCmp.VecOf R i Q Ω φv → ∀ (l₂ : Geo.Tor.Level H) (φ : (Fin (Vc D i).rank → LevQc Dw l₂) → ℂ), GlobalTheory.OnCmp.PhiOf R i Q Ω ι (Mfr l₂ • ⊤) φ → (∀ PP, PP ∈ R.Pg ∨ PP ∈ Q → l₂.Mb ≤ PP.asIdeal ∧ ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (R.Pg ∪ Q) → φv = ((Nat.card (Fin (Vc D i).rank → LevQ Dw l₂) : ℂ))⁻¹ • ∑ᶠ q : Fin (Vc D i).rank → LevQ Dw l₂, hatC l₂ φ q • heisO R.ψ (Vc D i) (Wc D i) (Matrix.of fun a b => e * incA D (((δ : ℤ) : D.host.E) * ι (cSep l₂ • levRep (q b)) a / (l₂.M : D.host.E))) (R.vacP i) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i hV H Dw ι hι hI
  obtain ⟨ε, hε⟩ := hI
  refine ⟨ε, fun χ Q Ω ω φv _ _ hRO hVec l φ hφ hP e he => ?_⟩
  obtain ⟨hvac, e₁, he₁, hθ⟩ := hVec
  obtain ⟨e₂, he₂, hφ⟩ := hφ
  obtain rfl := idemSum_unique (Vc D i) he₁ he
  obtain rfl := idemSum_unique (Vc D i) he₂ he
  have hβV := hR.lev.βV i
  have hβW := hR.lev.βW i
  have hS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβV
  have hT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hβW
  have hstd : R.ΛV i = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβV, ← GlobalTheory.SplitReps.hLat_one, hV.2]
  have hlat := mem_latRat_iff hV.1 hstd hβW
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  have hM' : (l.M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have hsurj : ∀ M ∈ GlobalTheory.LatVac.latRat (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)), ∃ x : Fin (Vc D i).rank → Dw.La, M = Matrix.of fun a b => ι (x b) a := by
    intro M hM
    choose x hx using fun b => hι.2.ge ((hlat M).1 hM b)
    exact ⟨x, Matrix.ext fun a b => (congrFun (hx b) a).symm⟩
  have hint : ∀ u ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True),
      IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u)) := fun u hu =>
    int_of_mem_latO (fun M hM => by
      obtain ⟨x, rfl⟩ := hsurj M hM
      exact (hφ x).1) hu
  have : Finite (LevQ Dw l) := GlobalTheory.LevelPairing.finite_LevQ
  have := Fintype.ofFinite (Fin (Vc D i).rank → LevQ Dw l)
  rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
  simp only [smul_smul]
  refine thetaAt_eq_sum _ _ hθ (fun q a b => ?_) fun w => ?_
  · rw [GlobalTheory.LatVac.cA_cA, Matrix.of_apply, ← mul_assoc, GlobalTheory.PlaceVec.idemSum_mul_self he]
  by_cases hw : w ∈ latO (Vc D i) (Wc D i) (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E))
      (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) (fun _ => True) ∧ IsHalf (cA D e) w
  swap
  · rw [halfInd, if_neg hw, zero_mul, if_neg]
    rintro ⟨h1, h2⟩
    have hN : ∀ PP ∈ R.Pg ∪ Q, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP h =>
      (hP PP (Finset.mem_union.1 hPP)).2 (by rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
    exact hw ⟨mem_latO_of_int hS hT hβV.choose_spec.1 hβW.choose_spec.1 he (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot)
      (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D) hN h1 h2, h1⟩
  have hw' : cA D e • w = w := Matrix.ext hw.2
  obtain ⟨M, hM0, u, hu, hwM⟩ := approx_mod (Nat.pos_of_ne_zero hM) hw.1
  obtain ⟨x, rfl⟩ := hsurj M hM0
  have hfr : frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w =
      uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b)) +
        l.M • frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (cA D e • u) := by
    rw [← hw', hwM, smul_add, GlobalTheory.PlaceVec.frMapAdj_add, frMapAdj_half, smul_comm]
    congr 1
    · exact one_smul _ _
    · exact (AddMonoidHom.mk' _ (GlobalTheory.PlaceVec.frMapAdj_add _ _ (R.βV i) (R.βW i))).map_nsmul _ _
  have hred : ∀ PP, PP ∈ R.Pg ∨ PP ∈ Q → redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) =
      redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b))) := fun PP hPP => by
    rw [hfr]
    have : Ideal.span {(l.M : 𝓞 D.host.E)} ≤ l.Mb := l.prod ▸ Ideal.mul_le_left
    exact GlobalTheory.PlaceVec.redM_add_nsmul PP ((hP PP hPP).1 (this (Ideal.subset_span rfl))) (hφ x).1 (hint u hu)
  rw [halfInd, if_pos hw, one_mul, if_pos ⟨hw.2, hw' ▸ hint w hw.1⟩,
    hRO _ (fun PP => redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e (fun b => ι (x b))))
      (fun PP h => hred PP (Finset.mem_union.1 h)), ← (hφ x).2, ← inversion l φ x]
  refine Finset.sum_congr rfl fun q _ => congrArg _ ?_
  have hY : (Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E)) =
      Matrix.of fun a b => (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) * ι (cSep l • levRep (q b)) a :=
    Matrix.ext fun a b => by simp only [Matrix.of_apply]; ring
  refine Eq.trans ?_ (char_eq (Y := Matrix.of fun a b => ((ε : ℤ) : D.host.E) * ι (cSep l • levRep (q b)) a / (l.M : D.host.E))
    hvac.1 hS hT (GlobalTheory.PlaceVec.idemSum_infPart he) hw.2 hu hwM ((hlat _).2 fun b => ?_)).symm
  · rw [hY, hRat_std hV.1 _ _ _ (by rw [star_div₀, star_intCast, star_natCast]), ← Complex.exp_int_mul]
    congr 1
    have h1 : ∀ c : ℚ, ∀ z : D.host.E, Algebra.trace ℚ D.host.E (D.host.xi0 * ((c : D.host.E) * z)) =
        c * Algebra.trace ℚ D.host.E (D.host.xi0 * z) := fun c z => by
      rw [mul_left_comm, ← Rat.smul_def, map_smul, smul_eq_mul]
    have h2 : ∀ y z, Dw.EF y z = -Dw.EF z y := fun y z => (LinearMap.IsAlt.neg Dw.alt z y).symm
    have h3 : ((pairL (l := l) x (fun b => levRep (q b)) : ℤ) : ℚ) = -(((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (D.host.xi0 *
        ∑ b, (Wc D i).hT ((Wc D i).frame.equivFun.symm (ι (cSep l • levRep (q b)))) ((Wc D i).frame.equivFun.symm (ι (x b))))) := by
      rw [pairL, Int.cast_sum, Finset.mul_sum, map_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun b _ => by rw [h2, Int.cast_neg, hε]
    have h4 := congrArg (fun z : ℚ => (z : ℂ)) h3
    rw [show (((ε : ℤ) : D.host.E) / (l.M : D.host.E)) = ((((ε : ℤ) : ℚ) / (l.M : ℚ) : ℚ) : D.host.E) by push_cast; rfl, h1]
    push_cast at h4 ⊢
    rw [h4]
    ring
  · have h1 := hι.2.le (LinearMap.mem_range_self ι ((ε : ℤ) • cSep l • levRep (q b)))
    convert h1 using 1
    funext a
    rw [map_zsmul, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, mul_div_cancel₀ _ hM', Pi.smul_apply, zsmul_eq_mul]

end GlobalTheory.DatumFourierOnCmp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleOfFreeStalksStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_bundle_of_free_stalks : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F] (r : ℕ), (∀ x : X, Nonempty (Module.Basis (Fin r) (X.presheaf.stalk x) (F.presheaf.stalk x :))) → IsVB F r := by
  first | exact @GlobalTheory.VB.isVB_of_basis_stalk | exact GlobalTheory.VB.isVB_of_basis_stalk | (intros; apply GlobalTheory.VB.isVB_of_basis_stalk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WatIffType
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.WatType

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_lift (R : RealDat D A Ks) (hg : R.models_gW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (hinj : Function.Injective (R.HW i σ).e) {x : (R.HW i σ).H} (hx : x ≠ 0) (g : G) :
    ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ := by
  by_contra hk
  apply hx
  have h0 : R.gW i σ g x = 0 := by
    apply hinj
    rw [hg i σ g x, map_zero]
    ext v h
    show actG0 _ _ _ _ _ h = 0
    unfold actG0
    rw [dif_neg hk]
    rfl
  have : R.gW i σ g⁻¹ (R.gW i σ g x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← this, h0, map_zero]

theorem mem_wat_iff (R : RealDat D A Ks) (F : Face D A) (hg : R.models_gW) (hW : R.models_HW) (b : Bool) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (x : (R.HW i σ).H) :
    (R.HW i σ).e x ∈ R.Wat i σ (R.levL F b σ) ↔
      (∀ p : (F.lvl b).P, postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG p)) ((R.HW i σ).e x) =
        σ ((((F.lvl b).ψ⁻¹ p : D.what₂.LLˣ)) : D.what₂.LL) • (R.HW i σ).e x) ∧
      ∑ g, σ ((idemOf A.X).coeff g) • postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) ((R.HW i σ).e x) =
        (R.HW i σ).e x := by
  have hx : (R.HW i σ).e x ∈ R.Wall i σ := (hW i σ).2.1 ▸ LinearMap.mem_range_self _ x
  unfold RealDat.Wall at hx
  unfold RealDat.Wat
  rw [mem_goodPart]
  rw [GlobalTheory.MultMem.mem_mult_iff] at hx ⊢
  refine and_congr ?_ ?_
  · constructor
    · intro h1 g
      by_cases h0 : x = 0
      · simp [h0]
      ext v h
      have hmem : R.eG g ∈ (R.levL F b σ).H := by
        show R.eG.symm (R.eG g) ∈ (F.lvl b).P
        rw [MulEquiv.symm_apply_apply]; exact g.2
      have h2 := GlobalTheory.LevelRows.levelType_eigenfunction_of_liftable_element (V := Wc D i) (β := R.βW i) (L := R.datWp i R.triv) (P := R.levL F b σ)
        (F := (R.HW i σ).e x v) (fun κ hκ h => h1.lev v κ hκ h) ⟨R.eG g, hmem⟩ (exists_lift R hg i σ (hW i σ).1 h0 g)
      have h3 : (R.eG.symm.toMonoidHom.subgroupComap (F.lvl b).P) ⟨R.eG g, hmem⟩ = g :=
        Subtype.ext (R.eG.symm_apply_apply g)
      refine (congrFun h2 h).trans ?_
      show σ (((F.lvl b).ψ⁻¹ ((R.eG.symm.toMonoidHom.subgroupComap (F.lvl b).P) ⟨R.eG g, hmem⟩) : D.what₂.LLˣ) : D.what₂.LL) * _ = _
      rw [h3]
      rfl
    · intro h
      refine ⟨hx.aut, hx.cusp, fun v => ?_, hx.equiv, hx.cont⟩
      have hP : IsPLevel (Wc D i) (R.βW i) (R.datWp i R.triv) (R.levL F b σ) ((R.HW i σ).e x v) := by
        refine ⟨fun κ hκ y => hx.lev v κ hκ y, fun p => ?_⟩
        have h1 := congrArg (fun z : MMap (R.MW i σ) => z v) (h ⟨R.eG.symm p.1, p.2⟩)
        have h2 : R.eG (R.eG.symm p.1) = p.1 := R.eG.apply_symm_apply p.1
        simp only [h2] at h1
        exact h1
      exact fun κ hκ y => hP.hasType κ hκ y
  · have h3 : ∀ v, R.eWf i σ ((R.HW i σ).e x v) = (∑ g, σ ((idemOf A.X).coeff g) •
        postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) ((R.HW i σ).e x)) v := by
      intro v
      simp only [RealDat.eWf, gaL, RealDat.eC, LinearMap.sum_apply, LinearMap.smul_apply, MultilinearMap.sum_apply,
        MultilinearMap.smul_apply, postOn_apply]
      rfl
    simp only [h3]
    exact ⟨fun h => MultilinearMap.ext h, fun h v => by rw [h]⟩

theorem wat_iff_type : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → Core R F → ∀ (b : Bool) i (x : (R.HW i (sg0 D A)).H), (R.HW i _).e x ∈ R.Wat i (sg0 D A) (R.levL F b (sg0 D A)) ↔ (eH R i x = x ∧ ∀ p : (F.lvl b).P, R.gW i (sg0 D A) p x = sg0 D A ((((F.lvl b).ψ⁻¹ p : D.what₂.LLˣ)) : D.what₂.LL) • x) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s _ hC b i x
  have hW := hC.models.HW
  have hg := hC.models.gW
  have hinj := (hW i (sg0 D A)).1
  rw [mem_wat_iff R F hg hW, and_comm]
  refine and_congr ?_ (forall_congr' fun p => ?_)
  · rw [← hinj.eq_iff]
    simp only [eH, RealDat.eC, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, hg i _ _ x]
  · rw [← hinj.eq_iff, hg, map_smul]

end GlobalTheory.WatType

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerRelationPassesToSemiLocalSpanStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_relation_passes_to_semi_local_span : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V → ∀ (t : GA E a) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS E a S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, ∀ x ∈ GlobalTheory.JSW.supS E a S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  first | exact @GlobalTheory.JSW.MirSemi.whit_rel_locSpan | exact GlobalTheory.JSW.MirSemi.whit_rel_locSpan | (intros; apply GlobalTheory.JSW.MirSemi.whit_rel_locSpan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordReachingIrreducibleKModuleReachesHighestWeigStatement
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_reaching_irreducible_k_module_reaches_highest_weight : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → KUnit ε E → ∀ L : Submodule ℂ V, FiniteDimensional ℂ L → KStab ε E L → ∀ Λ : Fin n → ℝ, (∀ ν : Fin n → ℝ, ∀ x ∈ L, x ≠ 0 → KHighest ε E ν x → ν = Λ) → ∀ (μ : Fin n → ℝ) (w : V), KHighest ε E μ w → ∀ (s t : Bool) (l : List (Fin n × Fin n)), (∀ p ∈ l, ε p.1 = s ∧ ε p.2 = t) → ∀ x ∈ L, ⟪x, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod w⟫_ℂ ≠ 0 → ∃ l' : List (Fin n × Fin n), l'.length = l.length ∧ (∀ p ∈ l', ε p.1 = s ∧ ε p.2 = t) ∧ μ + (l'.map fun p : Fin n × Fin n => root p.1 p.2).sum = Λ := by
  first | exact @GlobalTheory.HdStep.main | exact GlobalTheory.HdStep.main | (intros; apply GlobalTheory.HdStep.main <;> assumption)
end

