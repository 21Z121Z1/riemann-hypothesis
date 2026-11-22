import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0943
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0160
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2031
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0945
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0941
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0946
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateDefiniteFormsDescendNumberField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjDesc

set_option maxHeartbeats 1600000 in

theorem vals : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (a : Tp) (x₀ : A.fam.amb.FL i (tup a)) (h : GA D (Vc D i)), ∃ x : VsV D i M.c'.F, (R.HV i (tup a)).e (jVx R i (tup a) x₀) (fin _ h) = M.c0' x := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC i Tp tup M hP a x₀ h
  obtain ⟨_, _, _, hT, hc⟩ := hP.lift.c0
  obtain ⟨x, hx⟩ := GlobalTheory.RationalValues.placeEx R i M.jL (inC M.c') (tup a) (fun _ : Unit => h) M.c0' hC.models.jV hT hc hC.lev
    hC.grp.chiW hC.fam.pl_onto hC.fam.muVal x₀
  exact ⟨x (), hx ()⟩

set_option maxHeartbeats 1600000 in

theorem c_inj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → Function.Injective c := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ i Tp tup M hP c hc
  obtain ⟨gramR, c0R, c0L, hFT, hC0⟩ := hP.lift.c0
  have hfield : (inC M.c').comp M.jL = D.what₂.embLL := hP.lift.field
  have hbas : ∀ j, c (GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) j)) =
      c0L i (bVV D.what₂.LL (lamV D i) j) := fun j => by
    obtain ⟨v', hv', hcv'⟩ := hC0 (bVV D.what₂.LL (lamV D i) j)
    refine (hc v' _ ?_).trans hcv'
    rw [GlobalTheory.CoefModel.mapVV_coe, hv', MvPolynomial.map_map, hfield]
  have hli : LinearIndependent ℂ fun j => c (GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) j)) := by
    have h := (hFT.mapL i).2.1
    simp only [← hbas] at h
    exact h
  have hli0 := GlobalTheory.CoefModel.linearIndependent_mapVV D.what₂.embLL (lamV D i)
  have hsp0 := GlobalTheory.CoefModel.span_mapVV D.what₂.embLL (lamV D i)
  let B := Module.Basis.mk hli0 hsp0.ge
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have hs := B.sum_repr z
  have h0 : ∑ j, B.repr z j • c (GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) j)) = 0 := by
    calc _ = c (∑ j, B.repr z j • B j) := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_smul, Module.Basis.mk_apply]
      _ = 0 := by rw [hs, hz]
  have hc0 := Fintype.linearIndependent_iff.1 hli _ h0
  rw [← hs]
  exact Finset.sum_eq_zero fun j _ => by rw [hc0 j, zero_smul]

set_option maxHeartbeats 4000000 in

theorem conj_desc : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → (∀ t x, ((R.xi (tup t) x : Circle) : ℂ) ∈ M.c'.F) → ∀ a b : Tp, ConjTup R τ (tup a) (tup b) → ∀ (y : (R.HV i (tup a)).H) (y' : (R.HV i (tup b)).H), ConjForm R i τ c (tup a) (tup b) y y' → ∃ (n : ℕ) (α : Fin n → ℂ) (ys : Fin n → (R.HV i (tup a)).H) (ys' : Fin n → (R.HV i (tup b)).H), y = ∑ k, α k • ys k ∧ y' = ∑ k, τ (α k) • ys' k ∧ ∀ k (h : GA D (Vc D i)), ∃ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) ∧ (R.HV i (tup a)).e (ys k) (fin _ h) = M.c0' x ∧ (R.HV i (tup b)).e (ys' k) (fin _ h) = M.c0' x' := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hFW i Tp tup M hP τ ta hta hFix c hc hxi a b hab y y' hy
  obtain ⟨φ, hφs, hφ⟩ := GlobalTheory.T.exists_galoisConj_definiteForms_semilinearEquiv D G Pl0 T0 A T R F κ v₀ hC hFW i Tp tup M hP c hc τ (tup a) (tup b) hFix hab
  have hy' : y' = φ y := (hφ y y').1 hy
  have hmem : y ∈ Submodule.span ℂ (Set.range (R.jV i (tup a))) := by
    rw [GlobalTheory.HeckeClassSums.span_jV hC.models.HV hC.models.jV i (tup a)]; exact Submodule.mem_top
  obtain ⟨n, α, g, hg⟩ := Submodule.mem_span_set'.1 hmem
  have hinj := c_inj D G Pl0 T0 A T R κ v₀ i Tp tup M hP c hc
  refine ⟨n, α, fun k => (g k : (R.HV i (tup a)).H), fun k => φ (g k : (R.HV i (tup a)).H), hg.symm, ?_, ?_⟩
  · subst hy' hg
    exact (map_sum φ _ _).trans (Finset.sum_congr rfl fun k _ => hφs _ _)
  · intro k h
    have hk : ∃ x₀ : A.fam.amb.FL i (tup a), R.jV i (tup a) x₀ = (g k : (R.HV i (tup a)).H) := (g k).2
    obtain ⟨x₀, hx₀⟩ := hk
    have hv := vals D G Pl0 T0 A T R F κ v₀ hC i Tp tup M hP
    have hv2 := hv a x₀ h
    let x := hv2.choose
    have hx : (R.HV i (tup a)).e (jVx R i (tup a) x₀) (fin _ h) = M.c0' x := hv2.choose_spec
    have hx' : ((g k : (R.HV i (tup a)).H)) = jVx R i (tup a) x₀ := hx₀.symm
    have hcf := (hφ (g k : (R.HV i (tup a)).H) (φ (g k))).2 rfl h
    let x1 := hcf.choose
    let x1' := hcf.choose_spec.choose
    have hcv : ConjVec i τ x1 x1' := hcf.choose_spec.choose_spec.1
    have h1 : (R.HV i (tup a)).e (g k : (R.HV i (tup a)).H) (fin _ h) = c x1 := hcf.choose_spec.choose_spec.2.1
    have h1' : (R.HV i (tup b)).e (φ (g k : (R.HV i (tup a)).H)) (fin _ h) = c x1' := hcf.choose_spec.choose_spec.2.2
    let xC : VsV D i ℂ := GlobalTheory.CoefModel.mapVV (inC M.c') (lamV D i) x
    have hxC : c xC = M.c0' x := hc x xC rfl
    have e0 : (R.HV i (tup a)).e (g k : (R.HV i (tup a)).H) (fin _ h) = M.c0' x := by rw [hx']; exact hx
    have e1 : c x1 = c xC := h1.symm.trans (e0.trans hxC.symm)
    have hx1 : x1 = xC := hinj e1
    let x' : VsV D i M.c'.F := ⟨MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank),
      GlobalTheory.Proof.TensorMapDescent.map_mem_VV (ta : M.c'.F →+* M.c'.F) (lamV D i) _ x.2⟩
    have hcomp : (τ : ℂ →+* ℂ).comp (inC M.c') = (inC M.c').comp (ta : M.c'.F →+* M.c'.F) := by
      ext z; exact (hta z).symm
    have hx1' : (x1' : Pol ℂ D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (inC M.c') (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) := by
      rw [hcv, hx1]
      show MvPolynomial.map (τ : ℂ →+* ℂ) (MvPolynomial.map (inC M.c') (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank)) =
        MvPolynomial.map (inC M.c') (MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank))
      rw [MvPolynomial.map_map, MvPolynomial.map_map, hcomp]
    exact ⟨x, x', rfl, e0, h1'.trans (hc x' x1' hx1')⟩

end GlobalTheory.ConjDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisRationalFormsLocalUnitBall
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocBasis

theorem exists_basis_of_loc (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
    (V : Type) [AddCommGroup V] [Module K V] (N : Set V)
    (h0 : (0 : V) ∈ N) (hadd : ∀ f ∈ N, ∀ g ∈ N, f + g ∈ N)
    (hsm : ∀ (x t : 𝓞 K), t ∉ P.asIdeal → ∀ f ∈ N, ((x : K) / (t : K)) • f ∈ N)
    (hsp : ∀ f : V, ∃ c : K, c ≠ 0 ∧ c • f ∈ N)
    (m : ℕ) (g : Fin m → V)
    (hbd : ∀ f ∈ N, ∃ t : 𝓞 K, t ∉ P.asIdeal ∧ ∃ c : Fin m → 𝓞 K, (t : K) • f = ∑ k, (c k : K) • g k) :
    ∃ (n : ℕ) (B : Module.Basis (Fin n) K V), (∀ s, B s ∈ N) ∧
      ∀ f ∈ N, ∀ s, ∃ x t : 𝓞 K, t ∉ P.asIdeal ∧ B.repr f s = (x : K) / (t : K) := by
  classical
  have hle : P.asIdeal.primeCompl ≤ nonZeroDivisors (𝓞 K) := fun t ht =>
    mem_nonZeroDivisors_of_ne_zero fun h => ht (h ▸ P.asIdeal.zero_mem)
  let R := Localization.subalgebra.ofField K P.asIdeal.primeCompl hle
  haveI : IsLocalization.AtPrime R P.asIdeal := (inferInstance : IsLocalization P.asIdeal.primeCompl R)
  haveI : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) P.ne_bot R
  have mk'_coe : ∀ (x : 𝓞 K) (t : P.asIdeal.primeCompl),
      ((IsLocalization.mk' R x t : R) : K) = (x : K) / ((t : 𝓞 K) : K) := by
    intro x t
    have ht : ((t : 𝓞 K) : K) ≠ 0 := by
      intro h
      exact t.2 ((show (t : 𝓞 K) = 0 by exact_mod_cast h) ▸ P.asIdeal.zero_mem)
    rw [eq_div_iff ht]
    have h := congrArg (algebraMap R K) (IsLocalization.mk'_spec R x t)
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
    exact h
  have memR : ∀ r : R, ∃ x t : 𝓞 K, t ∉ P.asIdeal ∧ (r : K) = (x : K) / (t : K) := by
    intro r
    obtain ⟨⟨x, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.asIdeal.primeCompl r
    exact ⟨x, t, t.2, mk'_coe x t⟩
  have inR : ∀ x t : 𝓞 K, t ∉ P.asIdeal → ∃ r : R, (r : K) = (x : K) / (t : K) :=
    fun x t ht => ⟨IsLocalization.mk' R x (⟨t, ht⟩ : P.asIdeal.primeCompl), mk'_coe x ⟨t, ht⟩⟩
  have smul_def : ∀ (r : R) (f : V), r • f = (r : K) • f := fun r f => rfl
  let NR : Submodule R V :=
    { carrier := N
      add_mem' := fun {a b} ha hb => hadd a ha b hb
      zero_mem' := h0
      smul_mem' := fun r f hf => by
        obtain ⟨x, t, ht, hr⟩ := memR r
        change r • f ∈ N
        rw [smul_def, hr]
        exact hsm x t ht f hf }
  let L : Submodule R V := Submodule.span R (Set.range g)
  have hNL : NR ≤ L := by
    intro f hf
    obtain ⟨t, ht, c, hc⟩ := hbd f hf
    have ht0 : (t : K) ≠ 0 := by
      intro h
      exact ht ((show t = 0 by exact_mod_cast h) ▸ P.asIdeal.zero_mem)
    have hf' : f = ∑ k, ((c k : K) / (t : K)) • g k := by
      have : f = (t : K)⁻¹ • ((t : K) • f) := by rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
      rw [this, hc, Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_smul, div_eq_inv_mul]
    rw [hf']
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨r, hr⟩ := inR (c k) t ht
    rw [← hr, ← smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  haveI : Module.Finite R L := Module.Finite.span_of_finite R (Set.finite_range g)
  haveI : NoZeroSMulDivisors R V := ⟨fun {r f} h => by
    rw [smul_def] at h
    rcases smul_eq_zero.1 h with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr h⟩
  haveI : NoZeroSMulDivisors R L := ⟨fun {r x} h =>
    (smul_eq_zero.1 (congrArg Subtype.val h : r • (x : V) = 0)).imp id fun h' => Subtype.ext h'⟩
  haveI : Module.IsTorsionFree R L := inferInstance
  haveI : Module.Free R L := Module.free_of_finite_type_torsion_free'
  obtain ⟨n, B'⟩ := Submodule.basisOfPidOfLE hNL (Module.Free.chooseBasis R L)
  let v : Fin n → V := fun s => ((B' s : NR) : V)
  have hliR : LinearIndependent R v :=
    B'.linearIndependent.map' NR.subtype (Submodule.ker_subtype NR)
  have hli : LinearIndependent K v := (LinearIndependent.iff_fractionRing R K).1 hliR
  have hexp : ∀ y : NR, (y : V) = ∑ s, ((B'.repr y s : R) : K) • v s := by
    intro y
    have h := congrArg (fun y : NR => (y : V)) (B'.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [← h]
    rfl
  have hspan : ⊤ ≤ Submodule.span K (Set.range v) := by
    intro f _
    obtain ⟨c, hc, hcf⟩ := hsp f
    have h1 : c • f ∈ Submodule.span K (Set.range v) := by
      rw [show c • f = ((⟨c • f, hcf⟩ : NR) : V) from rfl, hexp]
      exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
    have h2 := Submodule.smul_mem _ c⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
  let B := Module.Basis.mk hli hspan
  have hBv : ∀ s, B s = v s := fun s => Module.Basis.mk_apply hli hspan s
  refine ⟨n, B, fun s => ?_, fun f hf s => ?_⟩
  · rw [hBv]; exact (B' s).2
  · have e1 : f = B.equivFun.symm (fun s => ((B'.repr ⟨f, hf⟩ s : R) : K)) := by
      rw [Module.Basis.equivFun_symm_apply]
      simp only [hBv]
      exact hexp ⟨f, hf⟩
    have e2 : B.repr f s = ((B'.repr ⟨f, hf⟩ s : R) : K) := by
      have e3 := congrArg (fun u => B.equivFun u s) e1
      simp only [LinearEquiv.apply_symm_apply] at e3
      rw [← Module.Basis.equivFun_apply]
      exact e3
    obtain ⟨x, t, ht, hr⟩ := memR (B'.repr ⟨f, hf⟩ s)
    exact ⟨x, t, ht, e2.trans hr⟩

end GlobalTheory.LocBasis

namespace GlobalTheory.GeoTie

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw}
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}

theorem supLattice_fg (YS : NX.NExpRealS Rl cG S) (fw : FWTie T0 Rl.toRealDat κ v₀) (j : Fin D.R.m) : ((S.A ((j : ℕ) + 1)).MK).FG := by
  classical
  obtain ⟨m, g', hg'⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (GlobalTheory.GoodLat.Obj.mkFull_of_tie fw j).1
  have hsc : ∀ (a : S.Ks) (w : Fin (Rl.nW j) → D.what₂.LL),
      (YS.fi j).e.symm ((YS.fi j).eK a • w) = a • (YS.fi j).e.symm w := by
    intro a w
    rw [← algebraMap_smul D.what₂.LL ((YS.fi j).eK a) w, (YS.fi j).eK_LL, LinearEquiv.map_smul, algebraMap_smul]
  let d : 𝓞 T0.Q.c.F → 𝓞 S.Ks := fun c =>
    ⟨(YS.fi j).eK.symm (c : T0.Q.c.F), map_isIntegral_int (YS.fi j).eK.symm.toRingHom c.isIntegral_coe⟩
  refine Submodule.fg_iff_exists_fin_generating_family.2 ⟨m, fun k => (YS.fi j).e.symm (g' k), le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine ((YS.fi j).mkK _).2 ?_
    rw [LinearEquiv.apply_symm_apply, ← hg']
    exact Submodule.subset_span ⟨k, rfl⟩
  · intro x hx
    have h1 : (YS.fi j).e x ∈ Submodule.span (𝓞 T0.Q.c.F) (Set.range g') := by
      rw [hg']; exact ((YS.fi j).mkK x).1 hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 h1
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun k => d (c k), ?_⟩
    calc ∑ k, d (c k) • (YS.fi j).e.symm (g' k) = (YS.fi j).e.symm (∑ k, c k • g' k) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← algebraMap_smul T0.Q.c.F (c k) (g' k)]
          have e1 : ((c k : T0.Q.c.F)) = (YS.fi j).eK ((YS.fi j).eK.symm (c k)) := ((YS.fi j).eK.apply_symm_apply _).symm
          rw [show algebraMap (𝓞 T0.Q.c.F) T0.Q.c.F (c k) = (c k : T0.Q.c.F) from rfl, e1, hsc,
            ← algebraMap_smul S.Ks (d (c k))]
          rfl
      _ = x := by rw [hc, LinearEquiv.symm_apply_apply]

end GlobalTheory.GeoTie

namespace GlobalTheory.GeoTie

theorem locBall_basis_exists : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), (∀ f : NX.FmK S ((j : ℕ) + 1), ∃ c : S.Ks, c ≠ 0 ∧ c • f ∈ locBall YS fw iC b j) → ∃ (n : ℕ) (B : Module.Basis (Fin n) S.Ks (NX.FmK S ((j : ℕ) + 1))), (∀ s, B s ∈ locBall YS fw iC b j) ∧ ∀ g ∈ locBall YS fw iC b j, ∀ s, ‖embS S iC b (B.repr g s)‖ ≤ 1 := by
  intro D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC hiC b j hsp
  classical
  set P := placeAt (embS S iC b) with hP
  have hS1 : ∀ f ∈ locBall YS fw iC b j, ∃ t : 𝓞 S.Ks, t ∉ P.asIdeal ∧
      (show ↥(S.A ((j : ℕ) + 1)).WK from ((t : S.Ks) • f : NX.FmK S ((j : ℕ) + 1))).1 ∈ (S.A ((j : ℕ) + 1)).MK := by
    have hS1a : ∀ f ∈ locBall YS fw iC b j, ∀ y : (Rl.FW j).Pt (placeC YS iC b),
        (Rl.FW j).nrm (placeC YS iC b) y ⟨(YS.fi j).e (show ↥(S.A ((j : ℕ) + 1)).WK from f).1,
          ((YS.fi j).wk _).1 (show ↥(S.A ((j : ℕ) + 1)).WK from f).2⟩ ≤ 1 :=
      GlobalTheory.T.norm_le_one_of_mem_localUnitBall_side D Γ Pl0 I0 T1 A3 T0 Rl cG S YS κ v₀ fw i iC hiC b j
    intro f hf
    obtain ⟨s, hs, hsf⟩ := GlobalTheory.supLattice_localisation_of_unitBall _ _ _ _ _ (Rl.FW j)
      (GlobalTheory.GoodLat.Obj.mkFull_of_tie fw j).2 (placeC YS iC b) _ (hS1a f hf)
    have heK : ∀ a : S.Ks, (YS.fi j).eK a = eKs YS a := fun a =>
      (algebraMap T0.Q.c.F D.what₂.LL).injective (((YS.fi j).eK_LL a).trans (eKs_LL YS a).symm)
    let t : 𝓞 S.Ks := ⟨(YS.fi j).eK.symm (s : T0.Q.c.F), map_isIntegral_int (YS.fi j).eK.symm.toRingHom s.isIntegral_coe⟩
    have ht : eKs YS (t : S.Ks) = (s : T0.Q.c.F) := by
      rw [← heK]; exact (YS.fi j).eK.apply_symm_apply _
    refine ⟨t, ?_, ?_⟩
    · intro htP
      apply hs
      change ‖embC YS iC b (s : T0.Q.c.F)‖ < 1
      rw [← ht, embC_eKs]
      exact htP
    · refine ((YS.fi j).mkK _).2 ?_
      change (YS.fi j).e ((t : S.Ks) • (show ↥(S.A ((j : ℕ) + 1)).WK from f).1) ∈ (Rl.FW j).MK
      rw [← algebraMap_smul D.what₂.LL (t : S.Ks), LinearEquiv.map_smul, ← (YS.fi j).eK_LL, algebraMap_smul, heK, ht]
      rw [← algebraMap_smul T0.Q.c.F s] at hsf
      exact hsf
  have hS2 : ((S.A ((j : ℕ) + 1)).MK).FG := supLattice_fg YS fw j

  have hunit : ∀ t : 𝓞 S.Ks, t ∉ P.asIdeal → ‖embS S iC b (t : S.Ks)‖ = 1 := fun t ht =>
    le_antisymm (norm_int_le_one _ t) (not_lt.1 ht)
  have hloc : ∀ x t : 𝓞 S.Ks, t ∉ P.asIdeal → ‖embS S iC b ((x : S.Ks) / (t : S.Ks))‖ ≤ 1 := by
    intro x t ht
    rw [map_div₀, norm_div, hunit t ht, div_one]
    exact norm_int_le_one _ x

  have h0 : (0 : NX.FmK S ((j : ℕ) + 1)) ∈ locBall YS fw iC b j := by
    intro z
    rw [map_zero]
    simp [valC_zero]
  have hadd : ∀ f ∈ locBall YS fw iC b j, ∀ g ∈ locBall YS fw iC b j, f + g ∈ locBall YS fw iC b j := by
    intro f hf g hg z
    rw [map_add, Submodule.coe_add, valC_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf z) (hg z))
  have hsm : ∀ (x t : 𝓞 S.Ks), t ∉ P.asIdeal → ∀ f ∈ locBall YS fw iC b j,
      (((x : S.Ks) / (t : S.Ks)) • f) ∈ locBall YS fw iC b j := by
    intro x t ht f hf z
    rw [valC_cuspOf_smul, norm_mul]
    exact mul_le_one₀ (hloc x t ht) (norm_nonneg _) (hf z)
  obtain ⟨m, g0, hg0⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hS2
  have hgWK : ∀ k, g0 k ∈ (S.A ((j : ℕ) + 1)).WK := fun k => by
    have h : g0 k ∈ (S.A ((j : ℕ) + 1)).MK := hg0 ▸ Submodule.subset_span ⟨k, rfl⟩
    exact h.1
  let g : Fin m → NX.FmK S ((j : ℕ) + 1) := fun k => ⟨g0 k, hgWK k⟩
  have hbd : ∀ f ∈ locBall YS fw iC b j, ∃ t : 𝓞 S.Ks, t ∉ P.asIdeal ∧ ∃ c : Fin m → 𝓞 S.Ks,
      (t : S.Ks) • f = ∑ k, (c k : S.Ks) • g k := by
    intro f hf
    obtain ⟨t, ht, htf⟩ := hS1 f hf
    rw [← hg0] at htf
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 htf
    refine ⟨t, ht, c, Subtype.ext ?_⟩
    rw [← hc]
    change _ = (S.A ((j : ℕ) + 1)).WK.subtype (∑ k, (c k : S.Ks) • g k)
    refine Eq.trans ?_ (map_sum (S.A ((j : ℕ) + 1)).WK.subtype
      (fun k => ((c k : S.Ks) • g k : ↥(S.A ((j : ℕ) + 1)).WK)) Finset.univ).symm
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (algebraMap_smul S.Ks (c k) (g0 k)).symm
  obtain ⟨n, B, hB, hrep⟩ := GlobalTheory.LocBasis.exists_basis_of_loc S.Ks P (NX.FmK S ((j : ℕ) + 1))
    (locBall YS fw iC b j) h0 hadd hsm hsp m g hbd
  refine ⟨n, B, hB, fun f hf s => ?_⟩
  obtain ⟨x, t, ht, hx⟩ := hrep f hf s
  rw [hx]
  exact hloc x t ht

end GlobalTheory.GeoTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoefScale
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.ConjTwist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoefLatConj

open MvPolynomial

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
open GlobalTheory.SeriesTie.Scale in

theorem exists_coef_scale : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κw v₀) → IoExt R → ∀ i : Fin D.R.m, OMPins T R κw v₀ O i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ (B : Base (Vc D i) (Wc D i)), B.Good → BaseOf R i B → ∃ κ : ℂ, κ ≠ 0 ∧ (∀ x : VsV D i ℂ, R.ioP i (PiTensorProduct.tprod ℂ u) (c x) ∈ B.valSpace) ∧ ∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (R.ioP i (PiTensorProduct.tprod ℂ u) (c x)) = κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank) := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ O hC _ hio i hO c hc u hu B hB hBo
  have hcV : (R.cV i).Is := hC.models.cV i
  have hinf : IsInfFam R.θ := hBo.θ ▸ hB.frame.vac.2.inf

  obtain ⟨gramR, c0R, c0L, hft, hbc⟩ := hO.2.lift.c0
  have hfield : (inC (O i).c').comp (O i).jL = D.what₂.embLL := hO.2.lift.field
  obtain ⟨e, he0, he⟩ := GlobalTheory.CoefReal.exists_real_model (Vc D i) R.θ (R.cV i) (lamV D i) (c0L i) hinf hcV (hft.mapL i)
  have hce : c = e.toLinearMap := by
    refine LinearMap.ext_on_range (GlobalTheory.CoefModel.span_mapVV D.what₂.embLL (lamV D i)) fun k => ?_
    obtain ⟨v', hv', hv0⟩ := hbc (bVV D.what₂.LL (lamV D i) k)
    refine (hc v' _ ?_).trans (hv0.trans (he0 _).symm)
    change MvPolynomial.map D.what₂.embLL _ = _
    rw [hv', MvPolynomial.map_map, hfield]

  obtain ⟨u', w₀, hu', -, hw⟩ := FWT.IsChosenExtremalVector.io _ hO.2.lift.v0 hio
  have huu : u' = u := funext fun ρ => Subtype.ext ((hu' ρ).trans (hu ρ).symm)
  rw [huu] at hw

  have hT := io_act hC.lev hC.thP hB hBo.ψ hBo.θ hBo.sT hBo.BS hBo.BT hBo.mu0 hBo.eta (PiTensorProduct.tprod ℂ u)
  have hlam : B.w.lam = lamV D i := hBo.lam
  have hΔ : B.w.delta (Wc D i).rank = RealDat.Delta i := hBo.delta
  have hpq := GlobalTheory.CoefLatConj.pq_le hB
  have hirr : ∀ U : Submodule ℂ (R.cV i).W, (∀ h : GinfC (Vc D i), U.map ((R.cV i).ρ h) ≤ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => hcV.2.2.2.2 U fun h => by
      obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 h
      rw [map_mul, hcV.1 k hk, mul_one]
      exact hU ⟨a, ha⟩
  have hΔ0 := GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) i
  set x := PiTensorProduct.tprod ℂ u
  have hharm : ∀ w, R.ioP i x w ∈ harm (Wc D i).rank B.w B.F.BS := by
    rcases hirr ((harm (Wc D i).rank B.w B.F.BS).comap (R.ioP i x)) (fun h => by
      rintro _ ⟨w, hw', rfl⟩
      rw [Submodule.mem_comap, hT h h.2]
      exact fockGL_mem_harm _ _ _ hw') with h | h
    · have h0 : w₀ ∈ (harm (Wc D i).rank B.w B.F.BS).comap (R.ioP i x) := by
        rw [Submodule.mem_comap, hw, ← hΔ]
        exact delta_mem_harm _ _
      rw [h, Submodule.mem_bot] at h0
      rw [h0, map_zero] at hw
      exact absurd hw.symm hΔ0
    · exact fun w => (h ▸ Submodule.mem_top : w ∈ (harm (Wc D i).rank B.w B.F.BS).comap (R.ioP i x))

  haveI := hcV.2.2.2.1
  obtain ⟨κ, hcc⟩ := GlobalTheory.T.schur_equivariant_maps_proportional (GinfC (Vc D i)) (R.cV i).W (GLR D (Vc D i).rank → ℂ) (fun h => (R.cV i).ρ h)
    (fun h => LinearMap.funLeft ℂ ℂ fun y => (realGL R.θ (Vc D i) h)⁻¹ * y)
    (harmFn (Wc D i).rank B.w B.F.BS ∘ₗ R.ioP i x) (coefLin (lamV D i) ∘ₗ e.symm.toLinearMap) hirr
    ((coefLin_injective _).comp e.symm.injective)
    (by
      rintro _ ⟨w, rfl⟩
      have h1 : harmFn (Wc D i).rank B.w B.F.BS (R.ioP i x w) ∈
          (harm (Wc D i).rank B.w B.F.BS).map (harmFn (Wc D i).rank B.w B.F.BS) := Submodule.mem_map_of_mem (hharm w)
      rw [GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D _ _ B.w B.F.BS hB.wt hpq, hlam] at h1
      refine Submodule.span_le.2 ?_ h1
      rintro _ ⟨G', rfl⟩
      exact ⟨e G', congrArg (coefLin _) (e.symm_apply_apply G')⟩)
    (fun h w => funext fun y => by
      change harmFn _ B.w B.F.BS (R.ioP i x ((R.cV i).ρ h w)) y = harmFn _ B.w B.F.BS (R.ioP i x w) _
      rw [hT h h.2, ← hBo.θ]
      exact harmFn_fockGL _ _ _ _ _)
    (fun h w => funext fun y => by
      obtain ⟨v, rfl⟩ := e.surjective w
      change coefLin _ (e.symm ((R.cV i).ρ h (e v))) y = coefLin _ (e.symm (e v)) _
      rw [he h h.2, e.symm_apply_apply, e.symm_apply_apply]
      exact coefFn_translate _ _ _ _)
  subst hce
  refine ⟨κ, fun h0 => hΔ0 ?_, fun y => hharm _, fun y => ?_⟩
  · have h1 := LinearMap.congr_fun hcc w₀
    rw [h0, zero_smul, LinearMap.comp_apply, hw] at h1
    exact GlobalTheory.T.harmonic_polynomial_eq_zero_of_function D _ _ B.w B.F.BS hB.wt hpq _ (hw ▸ hharm w₀) h1
  · have h1 := LinearMap.congr_fun hcc (e y)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h1
    exact h1

set_option maxHeartbeats 4000000 in

theorem coefLat_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κw : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κw v₀) → IoExt R → ∀ i : Fin D.R.m, OMPins T R κw v₀ O i → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC (O i).c') (O i).c0' c → ∀ u : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ (B : Base (Vc D i) (Wc D i)), B.Good → BaseOf R i B → ∃ κ : ℂ, κ ≠ 0 ∧ (∀ x : VsV D i ℂ, harmFn (Wc D i).rank B.w B.F.BS (R.ioP i (PiTensorProduct.tprod ℂ u) (c x)) = κ • coefFn (RingHom.id ℂ) (lamV D i) (x : Pol ℂ D.what₂.Tau (Vc D i).rank)) ∧ (∀ P ∈ B.valSpace, ∃! x : VsV D i ℂ, P = R.ioP i (PiTensorProduct.tprod ℂ u) (c x)) ∧ ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (Oc : Subring ℂ), IsCoefRing σ emb Oc → (∀ h : Bridge.Gf (Vc D i), B.coefLat σ emb Oc h = Submodule.span Oc {P | ∃ Fv ∈ nabAtr emb (lamV D i) (B.latAt h), P = R.ioP i (PiTensorProduct.tprod ℂ u) (c (κ⁻¹ • GlobalTheory.CoefModel.mapVV σ (lamV D i) Fv))}) ∧ ∀ τ : ℂ ≃+* ℂ, (∀ a : K, τ (σ a) = σ a) → (∀ (h : Bridge.Gf (Vc D i)) (x x' : VsV D i ℂ), ConjVec i τ x x' → (R.ioP i (PiTensorProduct.tprod ℂ u) (c x) ∈ B.coefLat σ emb Oc h ↔ R.ioP i (PiTensorProduct.tprod ℂ u) (c ((τ κ / κ) • x')) ∈ B.coefLat σ emb (Oc.map (τ : ℂ →+* ℂ)) h)) ∧ ∀ (ψ1 ψ1' : Twist D Circle), ψ1.Good → ψ1'.Good → ConjChar τ ψ1 ψ1' → FixDat B τ → ∀ f f' : Bridge.Gf (Vc D i) → PolF D (Wc D i).rank (Vc D i).rank, (∀ h, ∃ x x' : VsV D i ℂ, ConjVec i τ x x' ∧ f h = R.ioP i (PiTensorProduct.tprod ℂ u) (c x) ∧ f' h = R.ioP i (PiTensorProduct.tprod ℂ u) (c ((τ κ / κ) • x'))) → (f ∈ B.mtLat σ emb Oc ψ1 ↔ f' ∈ B.mtLat σ emb (Oc.map (τ : ℂ →+* ℂ)) ψ1') := by
  intro D G _ _ Pl0 T0 A T _ R F κw v₀ O hC hFW hio i hO c hc u hu B hB hBo
  obtain ⟨κ, hκ0, hval, hκ⟩ := exists_coef_scale D G Pl0 T0 A T R F κw v₀ O hC hFW hio i hO c hc u hu B hB hBo
  let Φ : VsV D i ℂ →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank := R.ioP i (PiTensorProduct.tprod ℂ u) ∘ₗ c
  have hlam := hBo.lam
  refine ⟨κ, hκ0, hκ, existsUnique_eq Φ hB hlam hκ0 hval hκ, fun K _ _ σ emb Oc hcoef =>
    ⟨fun h => coefLat_eq_span Φ hB hlam hκ0 hval hκ σ emb Oc h,
      fun τ hτ => ⟨fun h x x' hx => conj_mem_iff Φ hlam hκ0 hval hκ σ emb Oc τ hτ h hx, ?_⟩⟩⟩
  intro ψ1 ψ1' h1 h1' hcc hfd f f' hff
  constructor
  · exact GlobalTheory.MtLatConj.mtLat_conj D i B hB hlam Φ κ hκ0 hval hκ K σ emb Oc hcoef τ hτ ψ1 ψ1' h1 h1' hcc hfd f f' hff
  · intro hf'
    have hτ' : ∀ a : K, τ.symm (σ a) = σ a := fun a => by rw [τ.symm_apply_eq, hτ]
    have hcoef' : IsCoefRing σ emb (Oc.map (τ : ℂ →+* ℂ)) :=
      ⟨hcoef.emb, fun a => Subring.mem_map.2 ⟨_, hcoef.int a, hτ _⟩⟩
    have hOO : (Oc.map (τ : ℂ →+* ℂ)).map (τ.symm : ℂ →+* ℂ) = Oc := by
      ext z
      constructor
      · intro hz
        obtain ⟨_, hw, rfl⟩ := Subring.mem_map.1 hz
        obtain ⟨b, hb, rfl⟩ := Subring.mem_map.1 hw
        simpa using hb
      · intro hz
        exact Subring.mem_map.2 ⟨τ z, Subring.mem_map.2 ⟨z, hz, rfl⟩, by simp⟩
    have hτ0 : τ.symm κ ≠ 0 := (map_ne_zero _).2 hκ0
    have key := GlobalTheory.MtLatConj.mtLat_conj D i B hB hlam Φ κ hκ0 hval hκ K σ emb (Oc.map (τ : ℂ →+* ℂ)) hcoef' τ.symm hτ' ψ1' ψ1 h1' h1
      hcc.symm hfd.symm f' f (fun h => by
        obtain ⟨x, x', hx, e1, e2⟩ := hff h
        have hx' : x' = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x := Subtype.ext hx
        have e3 : GlobalTheory.CoefModel.mapVV (τ.symm : ℂ →+* ℂ) (lamV D i) ((τ κ / κ) • x') = (κ / τ.symm κ) • x := by
          rw [map_smulₛₗ, hx', mapVV_symm_mapVV]
          congr 1
          simp [map_div₀]
        refine ⟨(τ κ / κ) • x', (κ / τ.symm κ) • x, (congrArg Subtype.val e3).symm, e2, ?_⟩
        rw [e1, smul_smul, show τ.symm κ / κ * (κ / τ.symm κ) = 1 by field_simp, one_smul]
        rfl) hf'
    rwa [hOO] at key

end GlobalTheory.CoefLatConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaLieAlgebraUnitaryGroupOfJacquetRallisStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemma_lieAlgebra_unitaryGroup_of_jacquetRallis : (∀ r : ℕ, GlobalTheory.JR.UnitMatch r) → UnitLemmaLie ∧ UnitLemmaGroup := by
  first | exact @GlobalTheory.UnitLemma.unitLemma_lie_and_group | exact GlobalTheory.UnitLemma.unitLemma_lie_and_group | (intros; apply GlobalTheory.UnitLemma.unitLemma_lie_and_group <;> assumption)
end

