import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3255
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0149
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0686
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3242
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3094
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2849
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2947
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0098
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3243
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalZEqMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.TraitRam

variable {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ}

theorem dim_eq (hn : 2 ≤ n) (hζ : IsUnit ζ) (T : Trait F) : T.A.g = g := by
  let K := AlgebraicClosure (FractionRing T.V)
  let k : Sp K ⟶ Sp (FractionRing T.V) := spMap (algebraMap (FractionRing T.V) K)
  have hK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp := (IsPullback.of_hasPullback T.A.A.hom k).paste_horiz T.cart.1
  have h1 : SmoothOfRelativeDimension T.A.g (pullback.snd T.A.A.hom k) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback T.A.A.hom k) T.A.smoothDim
  refine GlobalTheory.SiegDim.dim_geometric_fibre F.univ hn hζ hK (k ≫ T.y) ?_
  change SmoothOfRelativeDimension T.A.g (pullback.snd F.univ.A.hom (k ≫ T.y))
  rw [← hp.isoPullback_inv_snd]
  exact (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
    (IsPullback.of_horiz_isIso (fst := hp.isoPullback.inv) (g := 𝟙 _) ⟨by simp⟩) h1

theorem finrank_le (hn : 2 ≤ n) (hζ : IsUnit ζ) (T : Trait F) : Module.finrank ℤ T.D.toPre.X ≤ g := by
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have h := GlobalTheory.TateUnif.rank_add_dim hR T.semi T.U
  have e := dim_eq hn hζ T
  omega

theorem evalZ_eq_mul : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o), 2 ≤ n → IsUnit ζ → ∀ (F : SFam g n ζ) (T T' : Trait F) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V), Function.Injective f → IsLocalHom f → (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) → T'.y = spMap fK ≫ T.y → ∀ m : ℕ, Associated (f T.ϖ) (T'.ϖ ^ m) → ∀ φ : InvFun ℤ, IsPolFan id g φ → φ.evalZ T'.β = m * φ.evalZ T.β := by
  intro g n o _ ζ hn hζ F T T' f fK hf hl hK hy m hm φ hφ
  have hB : GlobalTheory.Mum.Base T'.V := ⟨⟨inferInstance, inferInstance, inferInstance, T'.complete⟩, inferInstance⟩
  have hid : spMap (RingHom.id (FractionRing T'.V)) = 𝟙 _ := Spec.map_id _
  obtain ⟨e, he⟩ := GlobalTheory.T.trait_lattices_iso_forms_proportional_ramification g n o ζ F T T' T'.V f (RingHom.id _) fK (RingHom.id _) hB inferInstance hf
    Function.injective_id hl inferInstance hK (fun _ => rfl) (by rw [hid, Category.id_comp, hy]) T'.ϖ m 1 T'.irr hm
    (by rw [pow_one]; rfl)
  have hon := hφ T.D.toPre.X (finrank_le hn hζ T)
  have hc : toReal T.β ∈ psdCone (id : ℤ → ℤ) T.D.toPre.X :=
    GlobalTheory.PolFan.TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 T.symm) fun x => by simpa using T.mono.nonneg 0 x
  rw [← evalR_toReal φ T.β, ← hon.homog _ hc m m.cast_nonneg,
    ← evalZ_pull φ (r := e.toIntLinearEquiv.toLinearMap) e.surjective, ← evalR_toReal]
  congr 1
  refine LinearMap.ext₂ fun a b => ?_
  have h := he a b
  rw [Nat.cast_one, one_mul] at h
  simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul]
  exact_mod_cast h.symm

end GlobalTheory.Poinc.TraitRam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFrobeniusPullbackCotangentModVersc
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem isHopfIdeal_kerIdeal {R A C : Type} [CommRing R] [CommRing A] [CommRing C]
    [HopfAlgebra R A] [HopfAlgebra R C] (f : C →ₐc[R] A) : (kerIdeal f).IsHopfIdeal R where
  counit_eq_zero x hx := by
    have hle : kerIdeal f ≤ augIdeal R A := by
      refine Ideal.map_le_iff_le_comap.mpr fun c hc => ?_
      have hc' : counit (R := R) c = 0 := by simpa using hc
      rw [Ideal.mem_comap, RingHom.mem_ker]
      simpa [CoalgHomClass.counit_comp_apply] using hc'
    simpa using hle hx
  map_mkQ_comul_eq_zero := by
    intro x hx
    let Q := A ⧸ kerIdeal f
    let q := Ideal.Quotient.mkₐ R (kerIdeal f)
    let Φ : A →ₐ[R] Q ⊗[R] Q := (Algebra.TensorProduct.map q q).comp (Bialgebra.comulAlgHom R A)
    have hqf : ∀ c : C, q (f c) = algebraMap R Q (counit (R := R) c) := by
      intro c
      have hmem : f (c - algebraMap R C (counit (R := R) c)) ∈ kerIdeal f := by
        refine Ideal.mem_map_of_mem (f : C →ₐ[R] A) ?_
        rw [RingHom.mem_ker]
        simp
      have h0 : q (f (c - algebraMap R C (counit (R := R) c))) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      rw [map_sub, map_sub, AlgHomClass.commutes, AlgHomClass.commutes, sub_eq_zero] at h0
      exact h0
    have hg : q.toLinearMap ∘ₗ (f : C →ₗ[R] A) = Algebra.linearMap R Q ∘ₗ counit :=
      LinearMap.ext hqf
    have hΦ : kerIdeal f ≤ RingHom.ker Φ := by
      refine Ideal.map_le_iff_le_comap.mpr fun c hc => ?_
      have hc' : counit (R := R) c = 0 := by simpa using hc
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change TensorProduct.map q.toLinearMap q.toLinearMap (comul (f c)) = 0
      rw [← CoalgHomClass.map_comp_comul_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp,
        hg]
      have hsplit : TensorProduct.map (Algebra.linearMap R Q ∘ₗ counit)
          (Algebra.linearMap R Q ∘ₗ counit) =
          TensorProduct.map (Algebra.linearMap R Q) (Algebra.linearMap R Q ∘ₗ counit) ∘ₗ
            LinearMap.rTensor C (counit (R := R) (A := C)) := by
        rw [LinearMap.rTensor, ← TensorProduct.map_comp, LinearMap.comp_id]
      rw [hsplit, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul, TensorProduct.map_tmul]
      simp [hc']
    exact hΦ hx
  antipode_mem := by
    have h0 : ((1 : WithConv (A →ₐ[R] A)).ofConv).comp (f : C →ₐ[R] A) =
        (1 : WithConv (C →ₐ[R] A)).ofConv := by
      ext c
      simp [CoalgHomClass.counit_comp_apply]
    have h1 : WithConv.toConv ((HopfAlgebra.antipodeAlgHom R A).comp (f : C →ₐ[R] A)) *
        WithConv.toConv (f : C →ₐ[R] A) = 1 := by
      have := AlgHom.convMul_comp_bialgHom_distrib
        (WithConv.toConv (HopfAlgebra.antipodeAlgHom R A)) (WithConv.toConv (AlgHom.id R A)) f
      rw [AlgHom.antipode_id_cancel, h0] at this
      apply WithConv.ofConv_injective
      rw [this]
      rfl
    have h2 : (HopfAlgebra.antipodeAlgHom R A).comp (f : C →ₐ[R] A) =
        (f : C →ₐ[R] A).comp (HopfAlgebra.antipodeAlgHom R C) :=
      congrArg WithConv.ofConv (eq_inv_of_mul_eq_one_left h1)
    have hS : ∀ c : C, HopfAlgebra.antipode R (f c) = f (HopfAlgebra.antipode R c) := fun c => by
      simpa using DFunLike.congr_fun h2 c
    have hle : kerIdeal f ≤ Ideal.comap (HopfAlgebra.antipodeAlgHom R A) (kerIdeal f) := by
      refine Ideal.map_le_iff_le_comap.mpr fun c hc => ?_
      rw [Ideal.mem_comap, Ideal.mem_comap]
      have hc' : counit (R := R) c = 0 := by simpa using hc
      change HopfAlgebra.antipode R (f c) ∈ kerIdeal f
      rw [hS]
      refine Ideal.mem_map_of_mem (f : C →ₐ[R] A) ?_
      rw [RingHom.mem_ker]
      simpa using hc'
    intro x hx
    exact hle hx

theorem isCocomm_of_surjective {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Bialgebra R A] [Bialgebra R B] [IsCocomm R A] (f : A →ₐc[R] B)
    (hf : Function.Surjective f) : IsCocomm R B := by
    refine ⟨LinearMap.ext fun b => ?_⟩
    obtain ⟨a, rfl⟩ := hf b
    have h1 := CoalgHomClass.map_comp_comul_apply f a
    have h2 := TensorProduct.map_comm (f : A →ₗ[R] B) (f : A →ₗ[R] B) (comul (R := R) a)
    have h3 := Coalgebra.comm_comul R a
    show TensorProduct.comm R B B (comul (f a)) = comul (f a)
    rw [← h1, ← h2, h3]

end GlobalTheory.PDiv

namespace GlobalTheory.PDivGroup

theorem exists_cobOne_relFrob_eq_zero_dUnit_eq (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    (h : (p : K) = 0) (G : PDivGroup p K) (w : Cot K ((frobTwist h G).A 1)) :
    ∃ (β : (frobTwist h G).A 1) (w' : Cot K (G.A 1)),
      cobOne K (G.A 1) ((relFrob h G).app 1 β) = 0 ∧
        dUnit K β = w + cotMap ((verschiebung h G).app 1) w' := by
    haveI : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr h
    set V := (verschiebung h G).app 1 with hV
    set F := (relFrob h G).app 1 with hF
    set J : Ideal ((frobTwist h G).A 1) := kerIdeal V with hJdef
    haveI hJ : J.IsHopfIdeal K := GlobalTheory.PDiv.isHopfIdeal_kerIdeal V
    let π : (frobTwist h G).A 1 →ₐc[K] (frobTwist h G).A 1 ⧸ J := Bialgebra.Quotient.mkBialgHom J
    have hπa : ∀ a, π a = Ideal.Quotient.mk J a := fun a => rfl
    have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
    haveI : IsCocomm K ((frobTwist h G).A 1 ⧸ J) := GlobalTheory.PDiv.isCocomm_of_surjective π hπ
    haveI : Module.Finite K ((frobTwist h G).A 1 ⧸ J) :=
      Module.Finite.of_surjective (π : (frobTwist h G).A 1 →ₗ[K] _) hπ
    have hJaug : ∀ x ∈ J, counit (R := K) x = 0 := fun x hx =>
      Submodule.IsCoideal.counit_eq_zero (I := J.restrictScalars K) hx

    have hπV : ∀ a : G.A 1, π (V a) = algebraMap K _ (counit (R := K) a) := by
      intro a
      have hmem : V (a - algebraMap K (G.A 1) (counit (R := K) a)) ∈ J := by
        refine Ideal.mem_map_of_mem (V : G.A 1 →ₐ[K] (frobTwist h G).A 1) ?_
        rw [RingHom.mem_ker]
        simp
      have h0 : π (V (a - algebraMap K (G.A 1) (counit (R := K) a))) = 0 := by
        rw [hπa]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      rw [map_sub, map_sub, AlgHomClass.commutes, AlgHomClass.commutes, sub_eq_zero] at h0
      exact h0

    have hdual : ∀ φ ∈ augIdeal K (CartierDual K ((frobTwist h G).A 1 ⧸ J)), φ ^ p = 0 := by
      intro φ hφ
      have hφ1 : φ 1 = 0 := by
        have : counit (R := K) φ = 0 := by simpa using hφ
        simpa using this
      have hχ : (CartierDual.map π φ) ^ p = 0 := by
        apply GlobalTheory.T.pow_char_eq_zero_of_kills_verschiebung p K h G 1
        intro a
        rw [CartierDual.map_apply, hπV, Algebra.algebraMap_eq_smul_one]
        change φ.ofConv (counit (R := K) a • 1) = 0
        rw [map_smul]
        change counit (R := K) a • φ 1 = 0
        rw [hφ1, smul_zero]
      have hχ' : CartierDual.map π (φ ^ p) = 0 := by rw [map_pow]; exact hχ
      apply CartierDual.ext_apply
      intro x
      obtain ⟨a, rfl⟩ := hπ x
      have := congrArg (fun χ : CartierDual K ((frobTwist h G).A 1) => χ a) hχ'
      simp only [CartierDual.map_apply] at this
      simpa using this
    obtain ⟨b, hb0, hbw⟩ := GlobalTheory.T.exists_primitive_with_cotangent_of_dual_height_one p K ((frobTwist h G).A 1 ⧸ J) hdual (cotMap π w)
    obtain ⟨β, rfl⟩ := hπ b

    have hker : RingHom.ker π ≤ RingHom.ker F := by
      intro a ha
      have haJ : a ∈ J := by
        rw [RingHom.mem_ker, hπa] at ha
        exact Ideal.Quotient.eq_zero_iff_mem.mp ha
      rw [RingHom.mem_ker]
      exact GlobalTheory.T.app_one_eq_zero_of_kernel_ideal_of_comp_eq_prime_smul p K (frobTwist h G) G (verschiebung h G) (relFrob h G)
        (relFrob_comp_verschiebung h G) a haJ
    have hFβ : F β = liftSurj π hπ F hker (π β) := (liftSurj_apply π hπ F hker β).symm

    have hrange : ∀ x : Cot K ((frobTwist h G).A 1), cotMap π x = 0 →
        x ∈ LinearMap.range (cotMap V) := by
      let Rg := LinearMap.range (cotMap V)
      let D₀ : (frobTwist h G).A 1 →ₗ[K] Cot K ((frobTwist h G).A 1) ⧸ Rg :=
        Rg.mkQ ∘ₗ AugCot.d (counitAlgHom K ((frobTwist h G).A 1))
      have hD₀ : ∀ a, D₀ a = Rg.mkQ (dUnit K a) := fun a => rfl
      have hD₀mul : ∀ a b, D₀ (a * b) =
          counit (R := K) a • D₀ b + counit (R := K) b • D₀ a := by
        intro a b
        rw [hD₀, hD₀, hD₀]
        change Rg.mkQ (AugCot.d _ (a * b)) =
          counit (R := K) a • Rg.mkQ (AugCot.d _ b) + counit (R := K) b • Rg.mkQ (AugCot.d _ a)
        rw [AugCot.d_mul]
        simp
      have hJD : ∀ x ∈ J, D₀ x = 0 := by
        intro x hx
        refine Submodule.span_induction (p := fun x _ => D₀ x = 0) ?_ ?_ ?_ ?_ hx
        · rintro _ ⟨c, hc, rfl⟩
          rw [hD₀, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact ⟨dUnit K c, cotMap_d V c⟩
        · exact map_zero D₀
        · intro u v _ _ hu hv
          rw [map_add, hu, hv, add_zero]
        · intro a u hu hu0
          rw [smul_eq_mul, hD₀mul, hu0, hJaug u hu, zero_smul, smul_zero, add_zero]
      let D : ((frobTwist h G).A 1 ⧸ J) →ₗ[K] Cot K ((frobTwist h G).A 1) ⧸ Rg :=
        (J.restrictScalars K).liftQ D₀ (fun x hx => hJD x hx) ∘ₗ
          (Submodule.Quotient.restrictScalarsEquiv K J).symm.toLinearMap
      have hD : ∀ a, D (Ideal.Quotient.mk J a) = D₀ a := fun a => rfl
      have hDmul : ∀ u v, D (u * v) = counit (R := K) u • D v + counit (R := K) v • D u := by
        intro u v
        obtain ⟨a, rfl⟩ := hπ u
        obtain ⟨b, rfl⟩ := hπ v
        rw [← map_mul, hπa, hπa, hπa, hD, hD, hD, hD₀mul]
        rfl
      let L := AugCot.lift (counitAlgHom K ((frobTwist h G).A 1 ⧸ J)) D
        (fun u v => by simpa using hDmul u v)
      have hL : L ∘ₗ cotMap π = Rg.mkQ := by
        apply AugCot.hom_ext
        intro a
        rw [LinearMap.comp_apply]
        change L (cotMap π (dUnit K a)) = Rg.mkQ (dUnit K a)
        rw [cotMap_d]
        change L (AugCot.d _ (π a)) = _
        rw [AugCot.lift_d, hπa, hD, hD₀]
      intro x hx
      have := congrArg (fun g => g x) hL
      simp only [LinearMap.comp_apply, hx, map_zero] at this
      exact (Submodule.Quotient.mk_eq_zero Rg).mp this.symm
    obtain ⟨w', hw'⟩ := hrange (dUnit K β - w) (by rw [map_sub, cotMap_d, hbw, sub_self])
    refine ⟨β, w', ?_, ?_⟩
    · rw [hFβ, ← pullTwo_cobOne, hb0, map_zero]
    · rw [hw']
      abel

end GlobalTheory.PDivGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomTriplePeriodConstDualStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bottom_triple_period_const_dual : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω' : ℂ, Ω' ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (h : GA D P'.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
            ∀ T', X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g = Ω' * u * P'.coord h T' := by
  first | exact @GlobalTheory.BotFormula.bottom_formula_small | exact GlobalTheory.BotFormula.bottom_formula_small | (intros; apply GlobalTheory.BotFormula.bottom_formula_small <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechDeRhamClassOfQuasiPeriodicFunctionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cechDeRham_class_of_quasiPeriodic_functions : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (k : A.left.affineOpens → (Fin g → ℂ) → ℂ) (q : u.Λ → ℂ), (∀ U, DifferentiableOn ℂ (k U) (pre u.ex U.1)) → (∀ U V : A.left.affineOpens, V ≤ U → IsReg u.ex V.1 (k V - k U)) → (∀ U a, IsReg u.ex U.1 fun z => fderiv ℂ (k U) z (Pi.single a 1)) → (∀ U (l : u.Λ), ∀ z ∈ pre u.ex U.1, k U (z + l) = k U z + q l) → ∃ x, IsPer u.ex u.Λ x q := by
  first | exact @GlobalTheory.CechPer.exists_isPer_of_quasiPeriodic | exact GlobalTheory.CechPer.exists_isPer_of_quasiPeriodic | (intros; apply GlobalTheory.CechPer.exists_isPer_of_quasiPeriodic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonScaleThetaConstantsAtTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SiegTh.TraitScale

theorem isUnit_natCast {o V : Type} [CommRing o] [CommRing V] [IsDomain V] (f : o →+* FractionRing V)
    (hf : ∀ a, f a ∈ Set.range (algebraMap V (FractionRing V))) {m : ℕ} (hm : IsUnit (m : o)) : IsUnit (m : V) := by
  obtain ⟨u, hu⟩ := hm.exists_right_inv
  obtain ⟨v, hv⟩ := hf u
  refine IsUnit.of_mul_eq_one v (IsFractionRing.injective V (FractionRing V) ?_)
  rw [map_mul, map_natCast, hv, map_one, ← map_natCast f, ← map_mul, hu, map_one]

theorem thList_transport {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {ρ : LB.Gen (L.pull (eSec G))}
    {m N : ℕ} {K : Type} [Field K] {x₁ x₂ : Sp K ⟶ S} (e : x₁ = x₂) {T : Over S} (h₁ : Over.mk x₁ ⟶ T)
    (h₂ : Over.mk x₂ ⟶ T) (he : h₁.left = h₂.left) (θ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T))
    {pt : Fin N → (Over.mk x₁ ⟶ G)} {c : Fin N → K} (H : ThList G L ρ m x₁ (VVRank.pullS G _ h₁ θ) pt c) :
    ∃ pt' : Fin N → (Over.mk x₂ ⟶ G), ThList G L ρ m x₂ (VVRank.pullS G _ h₂ θ) pt' c := by
  subst e
  obtain rfl : h₁ = h₂ := Over.OverMorphism.ext he
  exact ⟨pt, H⟩

theorem level_odd {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) :
    Odd (S.r * S.N) ∧ 3 ≤ S.r * S.N := by
  obtain ⟨j, -, hj⟩ := ρ.r_eq
  have ho : Odd (S.r * S.N) := by
    rw [hj, ρ.N_eq]
    exact (ρ.n_odd.pow).mul (ρ.n_odd.pow.pow)
  refine ⟨ho, ?_⟩
  have h2 : 2 ≤ S.r * S.N := le_trans S.N_ge (Nat.le_mul_of_pos_left _ S.r_pos)
  obtain ⟨t, ht⟩ := ho
  omega

theorem exists_scale : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (m N : ℕ) (e : Fin N → Ω), Odd m → 3 ≤ m → IsUnit (m : o) → N = m ^ (4 * S.g) → SymE ρ m e → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (emb : Ω →+* FractionRing V), (∀ a : o, emb (algebraMap o Ω a) ∈ Set.range (algebraMap V (FractionRing V))) → ∃ (K : Type) (_ : Field K) (io : FractionRing V →+* K) (N' : ℕ) (c : Fin N → K) (c' : Fin N' → K) (a : K), a ≠ 0 ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c b / a) ∧ Prim (io.comp (algebraMap V (FractionRing V))) (fun b => c' b / a) ∧ (∀ j, io (emb (e j)) = symTup c j) ∧ (∀ x, ∃ b, c' x ^ ((S.r * S.N) ^ 2) = io (emb (S.th b)) ^ ((S.r * S.N) ^ 2)) ∧ ∀ b, ∃ x, c' x ^ ((S.r * S.N) ^ 2) = io (emb (S.th b)) ^ ((S.r * S.N) ^ 2) := by
  intro o Ω _ _ _ _ S ρ m N e hm hm3 hmu hN hE V _ _ _ hV emb hemb
  letI := ρ.P.isAb.comm
  let K := AlgebraicClosure (FractionRing V)
  let io : FractionRing V →+* K := algebraMap _ _
  let i : S.R →+* K := (io.comp emb).comp S.R.val.toRingHom
  let y : Sp (FractionRing V) ⟶ Sp S.R := spMap (emb.comp S.R.val.toRingHom)
  have hmV : IsUnit (m : V) := isUnit_natCast (emb.comp (algebraMap o Ω)) hemb hmu
  have hkV : IsUnit ((S.r * S.N : ℕ) : V) := isUnit_natCast (emb.comp (algebraMap o Ω)) hemb S.unit
  have ne : ∀ {k : ℕ}, IsUnit (k : V) → (k : K) ≠ 0 := fun h => by
    have := h.map (io.comp (algebraMap V (FractionRing V)))
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨hko, hk3⟩ := level_odd ρ
  have hfib : PolFib ρ.P.A ρ.P.L S.g (spMap i ≫ 𝟙 (Sp S.R)) :=
    ρ.g_eq ▸ GlobalTheory.UMin.FibExist.polFib_of_point _ ρ.P K _
  obtain ⟨pt, c, H⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed _ ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen S.g m N K _
    (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) hm (ne hmV) hN hfib
  obtain ⟨pt', c', H'⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed _ ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen S.g (S.r * S.N) _ K _
    (SecAt.pull ρ.P.A ρ.P.L (x := 𝟙 (Sp S.R)) ρ.th₁ i) hko (ne hkV) rfl hfib
  have hx : spMap i ≫ 𝟙 (Sp S.R) = spMap io ≫ y := by
    rw [Category.comp_id, ← spMap_comp]
  have H2 : HasTh₂ ρ.P.A ρ.P.L ρ.rig m (S.r * S.N) (spMap io ≫ y) c c' :=
    hx ▸ (⟨_, pt, pt', GlobalTheory.UMin.isGenSec_real_pull o Ω S ρ K i, H, H'⟩ :
      HasTh₂ ρ.P.A ρ.P.L ρ.rig m (S.r * S.N) (spMap i ≫ 𝟙 (Sp S.R)) c c')
  obtain ⟨P, α, -, hα, hiso⟩ := GlobalTheory.UMin.FibExist.polFib_of_point _ ρ.P (FractionRing V) y
  have hS : (letI := P.isAb.comm; HypS P.A P.L) := by
    letI := P.isAb.comm
    exact GlobalTheory.SymBaseChange.hypS_baseChange _ _ ρ.P.A P.A y α ρ.P.L P.L ρ.P.isLB P.isLB hα hiso ρ.hypS
  obtain ⟨a, ha, h₁, h₂⟩ := GlobalTheory.T.thetaConstants_two_levels_primitive_at_trait _ ρ.P.A ρ.P.L ρ.rig ρ.P.isLB ρ.rig_gen V hV y P α hα hiso hS K io m (S.r * S.N)
    _ _ c c' hm hm3 hmV hko hk3 hkV H2
  obtain ⟨r₁, r₂⟩ := GlobalTheory.T.thetaConstantList_realisedSystem_up_to_rootsOfUnity o Ω S ρ K i _ pt' c' H'
  refine ⟨K, inferInstance, io, _, c, c', a, ha, h₁, h₂, ?_, r₁, r₂⟩
  have hz : spMap i ≫ 𝟙 (Sp S.R) = spMap (io.comp emb) ≫ spMap S.R.val.toRingHom ≫ 𝟙 (Sp S.R) := by
    rw [← Category.assoc, ← spMap_comp]
  obtain ⟨q, Hq⟩ := thList_transport hz _
    ((Over.homMk (spMap (io.comp emb)) rfl : Over.mk (spMap (io.comp emb) ≫ spMap S.R.val.toRingHom ≫ 𝟙 (Sp S.R)) ⟶
      Over.mk (spMap S.R.val.toRingHom ≫ 𝟙 (Sp S.R))) ≫
      (Over.homMk (spMap S.R.val.toRingHom) rfl :
        Over.mk (spMap S.R.val.toRingHom ≫ 𝟙 (Sp S.R)) ⟶ Over.mk (𝟙 (Sp S.R))))
    (spMap_comp _ _) _ H
  rw [← ThetaRuleCompare.pullS_comp] at Hq
  exact hE.2.2 K (io.comp emb) q c Hq

end GlobalTheory.SiegTh.TraitScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonZeroAmpleSectionsVertical
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem GlobalTheory.HSAmp.common_zero_of_le_dim : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (ℓ d : ℕ) (C : Set X) (e : Fin d → ℕ) (g : Fin d → X.functionField), ℓ.Prime → IsIrreducible C → IsClosed C → C ⊆ fib X ℓ → (d : WithBot ℕ∞) ≤ topologicalKrullDim C → (∀ j, 0 < e j ∧ g j ∈ P.H (e j) 0) → (C \ ⋃ j, NV P (e j) 0 (g j)).Nonempty := by
  intro k _ X _ p D hX P hA ℓ d
  induction d with
  | zero =>
    intro C e g hℓ hC hCc hCf hd hg
    obtain ⟨x, hx⟩ := hC.nonempty
    exact ⟨x, hx, by simp⟩
  | succ d ih =>
    intro C e g hℓ hC hCc hCf hd hg
    obtain ⟨C', h1, h2, h3, h4⟩ := GlobalTheory.T.exists_irreducible_codim_one_zero_ample_section_fibre k X p D hX P hA ℓ d (e 0) C (g 0) hℓ hC hCc hCf
      (by exact_mod_cast hd) (hg 0).1 (hg 0).2
    obtain ⟨x, hxC', hx⟩ := ih C' (fun j => e j.succ) (fun j => g j.succ) hℓ h1 h2
      (h3.trans (Set.diff_subset.trans hCf)) h4 (fun j => hg j.succ)
    refine ⟨x, (h3 hxC').1, ?_⟩
    simp only [Set.mem_iUnion, not_exists] at hx ⊢
    intro j
    refine Fin.cases ?_ (fun j => hx j) j
    exact (h3 hxC').2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeRhamClassOfRigidifiedExtensionStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deRham_class_of_rigidified_extension : ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → AllPrim (dp0 R) (𝟙 _) A → Function.Surjective (toH1O (A.hom ≫ 𝟙 _)) → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (x : G.RigExt), ∃ (c : primDR A) (x' : G.RigExt), IsCan t c x' ∧ G.rigToExt x' = G.rigToExt x := by
  first | exact @GlobalTheory.PtExt.exists_isCan_rigToExt_eq | exact GlobalTheory.PtExt.exists_isCan_rigToExt_eq | (intros; apply GlobalTheory.PtExt.exists_isCan_rigToExt_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenTranslateOrderTwoTorusStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_even_translate_order_two_torus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (P₁ : GlobalTheory.UU.CP G₁) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), GlobalTheory.LN.CDvr R' ∧ FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ LBIso (A₁.L.pull gen₁.hom.left) (P₁.L.L.pull (pullback.fst G₁.hom (jK R'))) ∧ LBIso (abelian₂ G₁ P₁.L.L) ((abelian₂ G P.L.L).pull β₂) ∧ EvenOn P₁ := by
  first | exact @GlobalTheory.Mum.exists_even_translate | exact GlobalTheory.Mum.exists_even_translate | (intros; apply GlobalTheory.Mum.exists_even_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughIsogenyOfKillsKernelStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_through_isogeny_of_kills_kernel : ∀ (K : Type) [Field K] (A B C : AbVar K) (q : A ⟶ B) (f : A ⟶ C), IsIsogeny q → (∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ q.hom = 1 → x ≫ f.hom = 1) → ∃ g : B ⟶ C, q ≫ g = f := by
  first | exact @GlobalTheory.AV.AbVar.exists_factor_of_isogeny | exact GlobalTheory.AV.AbVar.exists_factor_of_isogeny | (intros; apply GlobalTheory.AV.AbVar.exists_factor_of_isogeny <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisInvariantNbhdClosedFibreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_invariant_nbhd_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∃ H : G'.left.Opens, (∀ σ, a.act σ ⁻¹ᵁ H = H) ∧ (∀ g : G'.left, spMap ρ (G'.hom g) = closedPoint R → g ∈ H) ∧ IsCompact (H : Set G'.left) ∧ (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) := by
  first | exact @GlobalTheory.Mum.exists_invariant_nbhd_closedFibre | exact GlobalTheory.Mum.exists_invariant_nbhd_closedFibre | (intros; apply GlobalTheory.Mum.exists_invariant_nbhd_closedFibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivativeSubmoduleStableStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_rationality_of_reciprocity : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → KerRatAt := by
  first | exact @GlobalTheory.BigOn.Exp.SerBase.kerRatAt | exact GlobalTheory.BigOn.Exp.SerBase.kerRatAt | (intros; apply GlobalTheory.BigOn.Exp.SerBase.kerRatAt <;> assumption)
end

