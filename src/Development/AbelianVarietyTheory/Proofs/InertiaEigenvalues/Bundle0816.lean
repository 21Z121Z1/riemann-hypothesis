import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MeetsReferenceOfMeetsAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0738
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyAlgHomOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0691
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0692
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0715
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0057
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.IntegralSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1020
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsXiOKEvenRamified
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0311
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGaloisConjugatesHeckeCharTrivialOnRealIdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0963
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0757
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0790
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0787
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0783
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0773
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0340
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0436
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0604
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0711
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPartEigensystemIsTripleEigensystem
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.EigAll

theorem exists_smul_mem_of_mem_span {O K V : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (N : Submodule O V)
    {v : V} (hv : v ∈ Submodule.span K (N : Set V)) : ∃ d : O, d ≠ 0 ∧ d • v ∈ N := by
  let S : Submodule K V :=
    { carrier := {v | ∃ d : O, d ≠ 0 ∧ d • v ∈ N}
      add_mem' := by
        rintro a c ⟨d, hd, ha⟩ ⟨e, he, hc⟩
        refine ⟨d * e, mul_ne_zero hd he, ?_⟩
        rw [smul_add]
        refine N.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact N.smul_mem _ ha
        · rw [mul_smul]; exact N.smul_mem _ hc
      zero_mem' := ⟨1, one_ne_zero, by rw [smul_zero]; exact N.zero_mem⟩
      smul_mem' := by
        rintro c a ⟨d, hd, ha⟩
        obtain ⟨n, m, hm, rfl⟩ := IsFractionRing.div_surjective (A := O) c
        have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm
        have hmK : algebraMap O K m ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
        refine ⟨m * d, mul_ne_zero hm0 hd, ?_⟩
        have e1 : m • ((algebraMap O K n / algebraMap O K m) • a) = n • a := by
          rw [← algebraMap_smul K m, smul_smul, mul_div_cancel₀ _ hmK, algebraMap_smul]
        show (m * d) • ((algebraMap O K n / algebraMap O K m) • a) ∈ N
        rw [mul_comm, mul_smul, e1, smul_comm]
        exact N.smul_mem _ ha }
  have hle : Submodule.span K (N : Set V) ≤ S :=
    Submodule.span_le.2 fun x hx => ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  exact hle hv

theorem eq_zero_of_joint {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : ι → V →ₗ[K] V) (p : ι → Prop) (ev : ι → K) (M : Finset (ι → K)) :
    ∀ y : V, (∀ μ ∈ M, ∃ t, p t ∧ μ t ≠ ev t) → (∀ t, p t → T t y = ev t • y) →
      y ∈ Submodule.span K {z | ∃ μ ∈ M, ∀ t, p t → T t z = μ t • z} → y = 0 := by
  classical
  induction M using Finset.induction_on with
  | empty =>
    intro y _ _ hs
    have : {z : V | ∃ μ ∈ (∅ : Finset (ι → K)), ∀ t, p t → T t z = μ t • z} = ∅ := by
      ext z; simp
    rw [this, Submodule.span_empty, Submodule.mem_bot] at hs
    exact hs
  | insert μ0 M _ ih =>
    intro y hne hy hs
    obtain ⟨t0, hp0, hμ0⟩ := hne μ0 (Finset.mem_insert_self _ _)
    let L : V →ₗ[K] V := T t0 - μ0 t0 • LinearMap.id
    have hL : Submodule.span K {z | ∃ μ ∈ insert μ0 M, ∀ t, p t → T t z = μ t • z} ≤
        (Submodule.span K {z | ∃ μ ∈ M, ∀ t, p t → T t z = μ t • z}).comap L := by
      rw [Submodule.span_le]
      rintro z ⟨μ, hμ, hz⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      rcases Finset.mem_insert.1 hμ with rfl | hμ
      · have : L z = 0 := by
          simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hz t0 hp0, sub_self]
        rw [this]; exact Submodule.zero_mem _
      · have : L z = (μ t0 - μ0 t0) • z := by
          simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hz t0 hp0, sub_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨μ, hμ, hz⟩)
    have hLy : L y = (ev t0 - μ0 t0) • y := by
      simp only [L, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hy t0 hp0, sub_smul]
    have h0 := ih ((ev t0 - μ0 t0) • y) (fun μ hμ => hne μ (Finset.mem_insert_of_mem hμ))
      (fun t ht => by rw [map_smul, hy t ht, smul_comm]) (hLy ▸ hL hs)
    rcases smul_eq_zero.1 h0 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hμ0
    · exact h

variable {D : D7} {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
  {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
  {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
  {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}

open Classical in

def trEig (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Set (D.nexp.Fm i j b) :=
  {z | ∃ μ ∈ (Finset.univ.filter fun s : D.ntw.Sig i => D.ntw.jS i s = j ∧ D.ntw.side i s = b).image
      (fun s (t : ℕ × PlE D.host) => GlobalTheory.EigTie.sigEv s t.1 t.2),
    ∀ t : ℕ × PlE D.host, HkIdx i t.1 t.2 → D.nexp.hkF i j b t.1 t.2 z = μ t • z}

theorem good_part_le_span_triple_eigenvectors (Bs : SideB D cf Rw low Pq S hL eig θ) (hF : FullAll D) (i : D.ntw.Tw) (j : ℕ)
    (hj : j ∈ Finset.Icc 1 D.R.m) (b : Bool) :
    V0 D.nexp i j b ≤ Submodule.span (FractionRing (D.ntw.O i)) (trEig D i j b) := by
  classical
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  set K := FractionRing (D.ntw.O i)
  let Φ : K ⊗[D.ntw.O i] D.ntw.B i j b →ₗ[K] D.nexp.Fm i j b := (D.nexp.embB i j b).liftBaseChange K
  have hΦ : ∀ k P, HkIdx i k P → ∀ z, Φ (((D.ntw.hk i j b k P).baseChange K) z) = D.nexp.hkF i j b k P (Φ z) := by
    intro k P hP z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp only [Φ, LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, map_smul]
      rw [Bs.hk_emb i j b k P x h1 h2 hP.2.2.2 hP.2.2.1 hP.2.1]
    | add z w hz hw => simp only [map_add, hz, hw]

  have hrange : ∀ x : D.ntw.B i j b, D.nexp.embB i j b x ∈ Submodule.span K (trEig D i j b) := by
    intro x
    have hx : (1 : K) ⊗ₜ[D.ntw.O i] x ∈ (⊤ : Submodule K (K ⊗[D.ntw.O i] D.ntw.B i j b)) := trivial
    rw [← Bs.sigSpan i j b h1 h2] at hx
    have hx' := Submodule.mem_map_of_mem (f := Φ) hx
    rw [Submodule.map_span] at hx'
    have e : Φ ((1 : K) ⊗ₜ[D.ntw.O i] x) = D.nexp.embB i j b x := by
      show (D.nexp.embB i j b).liftBaseChange K ((1 : K) ⊗ₜ[D.ntw.O i] x) = _
      rw [LinearMap.liftBaseChange_tmul, one_smul]
    rw [e] at hx'
    refine Submodule.span_mono ?_ hx'
    rintro _ ⟨z, ⟨s, hs1, hs2, hz⟩, rfl⟩
    refine ⟨fun t => GlobalTheory.EigTie.sigEv s t.1 t.2, Finset.mem_image.2 ⟨s, by simp [hs1, hs2], rfl⟩, ?_⟩
    intro t ht
    rw [← hΦ t.1 t.2 ht, hz t.1 t.2 ht.1 ht.2.1 ht.2.2.1 ht.2.2.2, map_smul]
    rfl
  intro v hv
  obtain ⟨d, hd, hdv⟩ := exists_smul_mem_of_mem_span (K := K) (D.nexp.Bsup i j b) (by rw [hF i j hj b]; trivial)
  have hdV : d • v ∈ V0 D.nexp i j b := by
    rw [← algebraMap_smul K d v]; exact Submodule.smul_mem _ _ hv
  have hmem : d • v ∈ LinearMap.range (D.nexp.embB i j b) := by
    rw [Bs.tw.B_range i j b]; exact ⟨hdv, hdV⟩
  obtain ⟨x, hx⟩ := hmem
  have hdK : algebraMap (D.ntw.O i) K d ≠ 0 := by
    intro h; exact hd (IsFractionRing.injective (D.ntw.O i) K (h.trans (map_zero _).symm))
  have : v = (algebraMap (D.ntw.O i) K d)⁻¹ • (d • v) := by
    rw [← algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hdK, one_smul]
  rw [this, ← hx]
  exact Submodule.smul_mem _ _ (hrange x)

theorem sig_all_of_sideB : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ),
    NoFormsOff D → MeetsAll D → CommAll D → FullAll D → D.nexp.sig_all := by
  intro D cf Rw low Pq S hL eig θ Bs hN hM hC hF
  classical
  refine EigModel.sig_all_of hN hM hC ?_
  rintro i j hj b ev ⟨y, hyV, hy0, hyE⟩
  by_contra hno
  push_neg at hno
  apply hy0
  refine eq_zero_of_joint (fun t : ℕ × PlE D.host => D.nexp.hkF i j b t.1 t.2) (fun t => HkIdx i t.1 t.2)
    (fun t => ev t.1 t.2) _ y ?_ (fun t ht => hyE t.1 t.2 ht) (good_part_le_span_triple_eigenvectors Bs hF i j hj b hyV)
  intro μ hμ
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hμ
  obtain ⟨hs1, hs2⟩ := (Finset.mem_filter.1 hs).2
  obtain ⟨k, P, hk, hne⟩ := hno s hs1 hs2
  exact ⟨(k, P), hk, hne⟩

end GlobalTheory.TwInputs.EigAll

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypeFormReadingRightTranslateLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TypeRead

theorem actG_eG (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (u : G0g D.nd) (y : D.nexp.Fm i j b) :
    D.nexp.actG i j b u (Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i j b y) = Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i j b (D.nexp.actG i j b u y) := by
  have h := congrArg (fun z => MonoidAlgebra.lift (FractionRing (D.ntw.O i)) (Module.End (FractionRing (D.ntw.O i)) (D.nexp.Fm i j b)) (G0g D.nd)
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (D.nexp.actG i j b)) z y)
    (D.nexp.eAlg_central i b (MonoidAlgebra.single u 1))
  simp only [map_mul, MonoidAlgebra.lift_single, one_smul, Module.End.mul_apply] at h
  exact h.symm

theorem finite_group_acts_on_good_type_form_by_character (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (x : D.nexp.Fm i j b) (hx : x ∈ V0 D.nexp i j b)
    (u : G0g D.nd) (hu : u ∈ D.nexp.U) :
    D.nexp.actG i j b u x = ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) • x := by
  obtain ⟨f, hf, rfl⟩ := hx
  have hf' := (Submodule.mem_iInf _).1 hf ⟨u, hu⟩
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hf'
  rw [actG_eG]
  change Formalism.MainNotions.IntegralHeckeForms.eG D.nexp i j b ((D.nexp.actG i j b (⟨u, hu⟩ : D.nexp.U) : _ ≃ₗ[_] _) f) = _
  erw [hf']
  simp

end GlobalTheory.TypeRead

open GlobalTheory.TypeRead in

theorem GlobalTheory.TypeRead.rd_mul_lift : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ x ∈ V0 D.nexp i ((j : ℕ) + 1) b, ∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (κ : GA D (Wc D j)),
      Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b u) κ → ∀ g,
      Y.Z.rd i j b x (g * κ) = Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) *
        Y.Z.rd i j b x g := by
  intro D X E Y i j b x hx u hu κ hκ g
  have hA : ActRead (Y.Z.rd i j b) :=
    actRead_realRd D X.Γ X.Pl0 X.I0 X.T X.A3 X.core.Q.c.F X.R X.cG Y.S Y.YS X.geo.v₀ Y.Z.ρ Y.Z.good i j b _ Y.Z.pin X.unif
      X.char.models.HW
  rw [← hA u κ hκ x g, finite_group_acts_on_good_type_form_by_character D i _ b x hx u hu, map_smulₛₗ]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolysReachSmallFieldCoefficientFunctions
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IntExpOnto

theorem exists_harm_complex {D : D7} (m n : ℕ) (w : Weight D n) (B : GLR D n) (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m)
    (F : Pol ℂ D.what₂.Tau n) (hF : F ∈ VV ℂ w.lam) :
    ∃ P ∈ harm m w B, harmFn m w B P = coefFn (RingHom.id ℂ) w.lam F := by
  obtain ⟨s, hs⟩ := GlobalTheory.ExportSeries.DeltaExtremal.harmFn_delta D m n w B hw hm
  have hs0 : ((s : ℤ) : ℂ) ≠ 0 := by exact_mod_cast s.ne_zero
  have key : ∀ u : GLR D n, harmFn m w B (fockGL m w B u (w.delta m)) =
      ((s : ℤ) : ℂ) • Onto.coefLin w.lam (actP w.lam (invTrK (u * B)) (ten fun τ => extremal ℂ n (w.lam τ))) := fun u => by
    funext x
    rw [harmFn_fockGL, hs, Pi.smul_apply, smul_eq_mul]
    congr 1
    change _ = coefFn _ _ _ _
    rw [Onto.coefFn_actP, _root_.mul_inv_rev, mul_assoc]
  have hle : (VV ℂ w.lam).map (Onto.coefLin w.lam) ≤ (harm m w B).map (harmFn m w B) := by
    rw [GlobalTheory.OrbitSpan.VV_eq_span_orbit, harm, Submodule.map_span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have h2 := key (invTrK g * B⁻¹)
    rw [inv_mul_cancel_right, Onto.invTrK_invTrK] at h2
    refine (Submodule.smul_mem_iff _ hs0).1 ?_
    beta_reduce
    rw [← h2]
    exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩
  exact hle ⟨F, hF, rfl⟩

theorem exists_harm {D : D7} (m n : ℕ) (w : Weight D n) (B : GLR D n) (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m)
    {K : Type} [Field K] [CharZero K] (σ : K →+* ℂ) (F : VV K w.lam) :
    ∃ P ∈ harm m w B, harmFn m w B P = coefFn σ w.lam (F : Pol K D.what₂.Tau n) := by
  obtain ⟨P, hP, e⟩ := exists_harm_complex m n w B hw hm (MvPolynomial.map σ F.1) (GlobalTheory.Proof.TensorMapDescent.map_mem_VV _ _ _ F.2)
  refine ⟨P, hP, e.trans (funext fun x => ?_)⟩
  rw [coefFn, coefFn, MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]

theorem onto : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ (j : Fin D.R.m) b (F : VV ↥D.LL0 (Y.Z.ρ.B i j b).w.lam), ∃ P ∈ (Y.Z.ρ.B i j b).valSpace, harmFn (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS P = coefFn (Formalism.L2.Host.embLL0 D) (Y.Z.ρ.B i j b).w.lam (F : Pol ↥D.LL0 D.what₂.Tau (Vc D j).rank) := by
  intro _ _ _ D X E Y _ _ i _ j b F
  have hB := Y.Z.good.base i j b
  refine exists_harm _ _ _ _ hB.wt (fun τ => ?_) _ F
  have h1 := hB.sig τ
  have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
  rw [← h1] at h2
  exact h2.le

end GlobalTheory.IntExpOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterTwistProps
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NormOneTwist

variable {D : D7}

def quotC (D : D7) : (AE D)ˣ →* (AE D)ˣ :=
  MonoidHom.id _ / Units.map (sigR (AF D.host.F) D.sp.cm.sig).toMonoidHom

def finQuot (D : D7) : (AE D)ˣ →* (GlobalTheory.FinalJoin.AfE D)ˣ :=
  (Units.map (finPart D).toMonoidHom).comp (quotC D)

theorem finPart_mul_inv (x : (AE D)ˣ) :
    finPart D (x : AE D) * finPart D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
  rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]

theorem finQuot_val (x : (AE D)ˣ) :
    ((finQuot D x : (GlobalTheory.FinalJoin.AfE D)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      finPart D (x : AE D) * sigR (Af D.host.F) D.sp.cm.sig (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) := by
  show finPart D ((x : AE D) * sigR (AF D.host.F) D.sp.cm.sig ((x⁻¹ : (AE D)ˣ) : AE D)) = _
  rw [RingHom.map_mul, GlobalTheory.DetRootChar.finPart_sigR]

theorem normOne_finQuot (x : (AE D)ˣ) : GlobalTheory.FinalJoin.NormOne (finQuot D x) := by
  change _ * sigR (Af D.host.F) D.sp.cm.sig _ = 1
  rw [finQuot_val]
  exact GlobalTheory.DetOnto.norm_one _ (GlobalTheory.DetOnto.sigR_sigR D) (finPart_mul_inv x)

theorem finQuot_of_isDetRoot {V : HSp D} {g : GA D V} {x : (AE D)ˣ} (hx : IsDetRoot V g x) :
    finQuot D x = Matrix.GeneralLinearGroup.det (finHom V g) := by
  apply Units.ext
  have h1 := congrArg (finPart D) hx
  rw [RingHom.map_mul, GlobalTheory.DetRootChar.finPart_sigR] at h1
  rw [finQuot_val, h1, mul_assoc, ← RingHom.map_mul, finPart_mul_inv x, RingHom.map_one, mul_one,
    GlobalTheory.DetRootChar.finPart_det]

theorem finQuot_incA (e : D.host.Eˣ) :
    ((finQuot D (Units.map (incA D).toMonoidHom e) : (GlobalTheory.FinalJoin.AfE D)ˣ) : GlobalTheory.FinalJoin.AfE D) =
      (1 : Af D.host.F) ⊗ₜ[D.host.F] ((e : D.host.E) * D.sp.cm.sig ((e⁻¹ : D.host.Eˣ) : D.host.E)) := by
  rw [finQuot_val]
  show finPart D (incA D (e : D.host.E)) * sigR (Af D.host.F) D.sp.cm.sig (finPart D (incA D ((e⁻¹ : D.host.Eˣ) : D.host.E))) = _
  show ((1 : Af D.host.F) ⊗ₜ[D.host.F] (e : D.host.E)) *
    ((1 : Af D.host.F) ⊗ₜ[D.host.F] D.sp.cm.sig ((e⁻¹ : D.host.Eˣ) : D.host.E)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

def delta (xi : (GlobalTheory.FinalJoin.AfE D)ˣ →* ℂˣ) (hn : ∀ u, GlobalTheory.FinalJoin.NormOne u → ‖((xi u : ℂˣ) : ℂ)‖ = 1) :
    (AE D)ˣ →* Circle where
  toFun x := ⟨((xi (finQuot D x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hn _ (normOne_finQuot x))⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (show ((xi (finQuot D (x * y)) : ℂˣ) : ℂ) = ((xi (finQuot D x) : ℂˣ) : ℂ) * ((xi (finQuot D y) : ℂˣ) : ℂ) by
    rw [map_mul, map_mul, Units.val_mul])

end GlobalTheory.NormOneTwist

namespace GlobalTheory.NormOneTwist

variable {D : D7}

end GlobalTheory.NormOneTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertSatakeParametersAgreeUnderDictionary
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertDict

theorem satake_agree : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → (π.SphAt v → IsUnramU U w) ∧ ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → (∃ Dv : InertDatum L n v w, Dv.σw = s ∧ Dv.ϖ = ϖ) ∧ ∀ (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), Dv.σw = s → Dv.ϖ = ϖ → NG.SatAt π Dv α → ∃ α' : Fin (n / 2) → ℂˣ, (∀ i, (α' i : ℂ) = α i) ∧ HasSatAt U w s ϖ q α' := by
  intro L _ _ _ n F π U hD v w hO
  refine ⟨GlobalTheory.T.isUnramified_of_sphericalVector_dictionary L n F π U hD v w hO, fun s ϖ q hs hU => ?_⟩
  obtain ⟨hun, hns, hq⟩ := GlobalTheory.T.inert_of_unramifiedIsometricInvolution L v w hO s ϖ q hs hU
  refine ⟨GlobalTheory.T.exists_inertDatum_of_involution_uniformizer L n v w hO hun hns s ϖ hs (hq ▸ hU), fun Dv α hσ hϖ hsat => ?_⟩
  have hsph : π.SphAt v := by
    obtain ⟨f, hf, hf0, U0, hU0, hU0', -⟩ := hsat
    exact ⟨f, hf, hf0, fun κ hκ ht => hU0 κ ((hU0' κ ht).2 hκ)⟩
  obtain ⟨α0, h0⟩ := GlobalTheory.T.exists_satakeParameter_of_unramified_inert_definiteUnitary L n U hD.1 w hun hns s ϖ q hs hU (GlobalTheory.T.isUnramified_of_sphericalVector_dictionary L n F π U hD v w hO hsph)
  subst hσ hϖ hq
  have heq := GlobalTheory.T.inertSatake_heckeEigenvalues_algebraic_automorphic L n F π U hD v w hO Dv α hsat α0 h0
  have hnz := GlobalTheory.T.satakeParameter_ne_zero_of_sameTransform (w.adicCompletion L) Dv.ϖ Dv.σw _ n hU α α0 heq
  refine ⟨fun i => Units.mk0 (α i) (hnz i), fun i => rfl, ?_⟩
  obtain ⟨b, hb, hb2, p, hp, σ, hc, hs1, hs2⟩ := h0
  refine ⟨b, hb, hb2, p, hp, σ, hc, hs1, fun x hx hx0 => ?_⟩
  obtain ⟨a1, a2, a3⟩ := hs2 x hx hx0
  refine ⟨a1, a2, fun h hh => ?_⟩
  rw [a3 h hh, ← heq h hh]
  rfl

end GlobalTheory.InertDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvPlaceNormProductMemCoefficientRing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormUnit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem coprime_absNorm {K : Type} [Field K] [NumberField K] (l : ℕ) (hl : l.Prime)
    (P : HeightOneSpectrum (𝓞 K)) (hP : ((l : ℕ) : 𝓞 K) ∉ P.asIdeal) :
    Nat.Coprime l (Ideal.absNorm P.asIdeal) := by
  rw [Nat.Prime.coprime_iff_not_dvd hl]
  intro hd
  haveI : Fact l.Prime := ⟨hl⟩
  letI : Field (𝓞 K ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  have hfin : Finite (𝓞 K ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  haveI := Fintype.ofFinite (𝓞 K ⧸ P.asIdeal)
  have hc : l ∣ Fintype.card (𝓞 K ⧸ P.asIdeal) := by
    rw [Fintype.card_eq_nat_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]; exact hd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card l hc
  have h1 : (l : 𝓞 K ⧸ P.asIdeal) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
  have hx0 : x ≠ 0 := by
    rintro rfl; rw [addOrderOf_zero] at hx; exact hl.one_lt.ne hx
  have h2 : (l : 𝓞 K ⧸ P.asIdeal) = 0 := (mul_eq_zero.1 h1).resolve_right hx0
  apply hP
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact h2

theorem isUnit_natCast_of_coprime {R : Type} [CommRing R] [IsLocalRing R] {l n : ℕ}
    (hl : ((l : ℕ) : R) ∈ IsLocalRing.maximalIdeal R) (h : Nat.Coprime l n) : IsUnit ((n : ℕ) : R) := by
  by_contra hn
  have hn' : ((n : ℕ) : R) ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).2 hn
  obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 h : IsCoprime (l : ℤ) (n : ℤ))
  have e : (1 : R) = (a : R) * (l : R) + (b : R) * (n : R) := by
    have := congrArg (Int.cast : ℤ → R) hab
    push_cast at this
    exact this.symm
  have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [e]; exact add_mem (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hn')
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem normProd_inv_mem (D : D7) (ρ : Setup D.ntw) (i : D.ntw.Tw) (b : Bool) (Q : Finset (Pl D.host.E))
    (hQ : Disjoint Q (D.ntw.S0 i)) : ((normProd Q : ℕ) : ℂ)⁻¹ ∈ (ρ.eO i b).range := by
  have hcop : Nat.Coprime (D.ntw.l i) (normProd Q) := by
    unfold normProd
    refine Nat.Coprime.prod_right fun P hP => coprime_absNorm _ (D.ntw.lPrime i).out P fun hl => ?_
    exact Finset.disjoint_left.1 hQ hP (D.ntw.twistExcludedPlaces_contains_residueChar i hl)
  obtain ⟨u, hu⟩ := isUnit_natCast_of_coprime (D.ntw.O_l i) hcop
  refine ⟨(u⁻¹ : (D.ntw.O i)ˣ), ?_⟩
  have h1 : ρ.eO i b (u : D.ntw.O i) = ((normProd Q : ℕ) : ℂ) := by rw [hu, map_natCast]
  rw [← h1]
  exact map_units_inv (ρ.eO i b) u

end GlobalTheory.NormUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelsOfDepthZero
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.GoodAll

theorem goodFTAll_of_local : Green → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Rw : GlobalTheory.HeightCounting.RowSide D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (L : ∀ k, LabelDatum (D.host.g k)), GlobalTheory.HeightCounting.RowTrue hL D rep (fun σ w => T.e w (Rw.locR σ w)) Rw.satR → GlobalTheory.HeightCounting.RowDepth D rep → LabTie D L → (∀ k, TameGen.DepthZeroCuspidal (D.host.g k)) → (∀ (I : Ident D) rc, IsRc hL T I rc → ∀ k v, TameGen.TameParam (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v)) (fun π : Supp.GLRep _ => rc k v π.1 π.2)) → (∀ (I : Ident D) cp, IsComp I rep cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g D.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ a, ρ.asAlgebraHom a x ∈ W) ∧ ρ.asAlgebraHom D.ntypes.e0 x = x) → GoodFTAll D := by
  intro hG hZ hL D T Rw rep L hRow hDep hLT hDZ hTP hVec σ
  obtain ⟨I⟩ := GlobalTheory.T.nonempty_typePlaceCompletionIdent D
  obtain ⟨rc, hrc, hcls⟩ := GlobalTheory.T.exists_class_map_correspondence hL D T I
  obtain ⟨cp, hcomp, hcp⟩ := GlobalTheory.T.exists_type_components hL D T I rc hrc Rw rep hRow hDep
  have hP : LabParam D L rc :=
    GlobalTheory.SerSys.Bridge.labParam_of D L rc hG (GlobalTheory.T.tame_support_compatible hZ hL D T I rc hrc) hDZ (hTP I rc hrc)
  have hSC := GlobalTheory.T.seriesIdempotentStarCompatible_of_labelling_agree hG D L hLT
  obtain ⟨V, _, _, ρ, W, x, hconj, hx0, hxW, hxe⟩ := hVec I cp hcomp σ
  exact GlobalTheory.T.conjugate_type_vector D Rw L rc cp hLT hP hcls hSC hcp V ρ W σ hconj x hx0 hxW hxe

end GlobalTheory.GoodAll
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PAdicMonodromyTheoremMatrixForm
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem matThm_holds : MatThm :=
  GlobalTheory.T.padicMonodromyMatrixForm_of_induction_cases GlobalTheory.T.deRham_iff_framed_galois_representation GlobalTheory.T.lubinTateTwistTotalWeightZero_proof GlobalTheory.T.weightZero_potentiallySemistable_of_sen_theorem GlobalTheory.T.potentially_semistable_reducible_unramified_split GlobalTheory.T.monodromy_irreducible_elementary_weightModification

end GlobalTheory.PMon
end

