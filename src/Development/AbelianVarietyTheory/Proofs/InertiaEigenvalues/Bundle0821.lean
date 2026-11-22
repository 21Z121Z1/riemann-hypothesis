import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnivSupOfXi
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwInputs

theorem univSup_of_xi : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), FullTie hρ rd → Laws hρ rd → XiType rd → XiBdd rd → ∀ E : IntegralHeckeForms.XD D, UnivSup D E := by
  intro D ρ hρ rd F L hT hB E i hi j hj b a _
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hj1
  let j' : Fin D.R.m := ⟨n, hj2⟩
  have T := F.tie i j' b
  obtain ⟨c, hc⟩ := hB i hi j' b _ _ _ (T.dat a)
  refine ⟨c, fun Q M hs hcl hS hlev => ?_⟩
  have hQ : InRange D.ntw i Q := ⟨hs, hcl, hS⟩
  have hnp : ∀ v ∈ Q, ((normProd (T.supp a) : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal :=
    fun v hv h => Finset.disjoint_left.1 hlev hv ((T.lev_iff a v).2 h)
  obtain ⟨x, hx, he⟩ := T.thU_of_rat (L.rat i hi j' b).2.2 M hQ hlev
  classical
  refine ⟨∑ a', Finsupp.single (spread D.nexp i Q M (ρ.ch i) a') (x a'), ?_, fun δ => ?_⟩
  · rw [he, grpSum, ← Finsupp.sum_finsetSum_index (fun _ => by rw [TensorProduct.zero_tmul])
      (fun _ _ _ => by rw [TensorProduct.add_tmul])]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Finsupp.sum_single_index (by rw [TensorProduct.zero_tmul])]
  · have h0 : ∀ a', x a' ∈ Fm0 D.nexp i ((j' : ℕ) + 1) b :=
      fun a' => hT i hi j' b Q M hQ _ _ _ (T.dat a) hnp a' (x a') (hx a')
    have h1 : ∀ a', ((D.ntw.l i : D.ntw.O i) ^ c) • x a' ∈ D.nexp.Bsup i ((j' : ℕ) + 1) b :=
      fun a' => hc Q M hQ hnp a' (x a') (hx a')
    rw [Finsupp.finsetSum_apply]
    refine ⟨Submodule.sum_mem _ fun a' _ => ?_, ?_⟩
    · rw [Finsupp.single_apply]; split_ifs
      · exact h0 a'
      · exact zero_mem _
    · rw [Finset.smul_sum]
      refine Submodule.sum_mem _ fun a' _ => ?_
      rw [Finsupp.single_apply]; split_ifs
      · exact h1 a'
      · rw [smul_zero]; exact zero_mem _

end GlobalTheory.TwInputs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValCCuspOfSmul
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def embS {D : D7} (S : NX.RatDat D.ntw) {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool) :
    S.Ks →+* ℂ_[D.ntw.l i] :=
  iC.comp (NX.ιK S i b)

section Ball

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀) {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool)
  (j : Fin D.R.m)

theorem embC_eKs (a : S.Ks) : embC YS iC b (eKs YS a) = embS S iC b a := by
  simp only [embC, embS, RingHom.comp_apply, sideK_eKs]
  rfl

def locBall : Set (NX.FmK S ((j : ℕ) + 1)) :=
  {f | ∀ z : Pts YS iC b ((j : ℕ) + 1), ‖valC z.1 (cuspOf YS fw j f : T0.R ((j : ℕ) + 1))‖ ≤ 1}

variable {iC b} in
theorem valC_cuspOf_smul (z : FrC YS iC b ((j : ℕ) + 1)) (a : S.Ks) (f : NX.FmK S ((j : ℕ) + 1)) :
    valC z (cuspOf YS fw j (a • f) : T0.R ((j : ℕ) + 1)) = embS S iC b a * valC z (cuspOf YS fw j f : T0.R ((j : ℕ) + 1)) := by
  rw [cuspOf_smul, Submodule.coe_smul, valC_smul, embC_eKs]

end Ball

end GlobalTheory.GeoTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

def trSp (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (f₀ : WO V W → ℂ) (e : AE D) (M : ℕ) (O : Subring ℂ) :
    Submodule O (WO V W → ℂ) :=
  Submodule.span O {f | ∃ y : WO V W, IsHalf e y ∧ M • y ∈ latO V W ΛV ΛW (fun _ => True) ∧ f = heisO ψ V W y f₀}

abbrev stdF (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D)
    (sW BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f : WO V W → ℂ) :
    MvPolynomial (FVar D W.rank V.rank) ℂ →ₗ[ℂ] (WO V W → ℂ) :=
  pureTensorO ψ θ V W (fun _ => 1) sW (fun _ => 1) BW f

def OneAt (V : HSp D) (l : ℕ) (h : GA D V) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ((l : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal →
    ∀ a b, algebraMap (AF D.host.F) (AE D) ε * (Formalism.L2.Theta.mt V h - 1) a b = 0

def ChiData (χW : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (b : ℕ) : Prop :=
  ChrEq χW χ ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((b : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal → χ.UnrAt Q) ∧
    ∀ Q : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.IdemSupport.cP Q ≠ Q → ∀ k, χ.resFin (Q.under (𝓞 D.host.F)) k = 1

def ValRing {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ) : Prop :=
  ∀ x : k, la.valuation k x ≤ 1 → σ x ∈ O

def locRing {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) : Subring ℂ :=
  (la.valuation k).integer.map σ

theorem valRing_locRing {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) :
    ValRing σ la (locRing σ la) := fun x hx => ⟨x, hx, rfl⟩

theorem valRing_range {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) :
    ValRing σ la σ.range := fun x _ => ⟨x, rfl⟩

def ConjIn (D : D7) {k : Type} [Field k] (σ : k →+* ℂ) : Prop := ∀ (τ : D.host.E →+* ℂ) (a : D.host.E), ∃ x, σ x = τ a

def DenomAt {E : Type} [Field E] {n : ℕ} (l c : ℕ) (γ : GL (Fin n) E) : Prop :=
  ∃ m : ℕ, Nat.Coprime m l ∧ ∀ a b, IsIntegral ℤ (((m * l ^ c : ℕ) : E) * γ.val a b) ∧
    IsIntegral ℤ (((m * l ^ c : ℕ) : E) * γ⁻¹.val a b)

theorem oneAt_one (V : HSp D) (l : ℕ) : OneAt V l 1 := fun _ _ _ _ a b => by
  have h1 : Formalism.L2.Theta.mt V 1 = 1 := by unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
  rw [h1, sub_self]
  simp

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m)
  (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i)

def BaseCc (ph : ℂ) : Prop :=
  CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) T.σ₀) (castDict hV (T.dict ((i : ℕ) + 1) T.σ₀))
    (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) (T.x₀ ((i : ℕ) + 1) T.σ₀) (R.ωP i A.μ0) (R.vacP i)
    fun k => ph * T.cE ((i : ℕ) + 1) T.σ₀ k

def CovCc (ph : ℂ) (C : Cover T ((i : ℕ) + 1) T.σ₀) : Prop :=
  CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) C.U₂ (castDict hV C.dict₂)
    (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) (T.x₀ ((i : ℕ) + 1) T.σ₀) (R.ωP i A.μ0) (R.vacP i)
    fun k => ph * C.cc₂ k

end GlobalTheory.LevelSeries

end
end

