import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0365
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0306
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0381
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1934

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeTransformEqOfUnramifiedBaseChangeEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertUbcSatake

theorem satU_eq_of_ubc_eq : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K) (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ α β : Fin (n / 2) → ℂ, ubc n (Multiset.map α Finset.univ.val) = ubc n (Multiset.map β Finset.univ.val) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), Formalism.UG.SatU ϖ q h α = Formalism.UG.SatU ϖ q h β :=
  GlobalTheory.SatBcZero.satU_eq_of_ubc_eq

end GlobalTheory.InertUbcSatake
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeUnramifiedFrobeniusEigen
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LlcSplit

theorem locV_unr_frobEig_of_hasSatake : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (i : D.nd.Loc) (Q : D.naut.AV i) (sp : SplitPlace D.host.E) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E))) (α : Fin D.R.nV → ℂˣ), IsLocS (P.H.av.S i Q) sp σ → GlobalTheory.SmGL.HasSatake σ.ρ α → D.naut.unr (D.naut.locV i Q sp.w) ∧ D.naut.frobEig (D.naut.locV i Q sp.w) = Finset.univ.val.map (fun k => (((α k)⁻¹ : ℂˣ) : ℂ)) := by
  intro hL D P i Q sp σ α hS hα
  have h3 := P.au (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i Q) sp σ hS
  rw [← P.H.emb i Q, ← D.nbc.embAV_loc i Q sp.w,
    GlobalTheory.CuspRep.ParLaws.rec_eq_diag (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 sp.w)) hα] at h3
  have hu : D.naut.unr (D.naut.locV i Q sp.w) :=
    (P.T.unr _ _).2 (by rw [h3]; exact (GlobalTheory.WeilDeligne.WD.unr_mk _).2 (GlobalTheory.WeilDeligne.WDRep.unr_diag _))
  refine ⟨hu, ?_⟩
  rw [P.T.frobEig _ _ hu, h3, GlobalTheory.WeilDeligne.WD.frobEig_diag]

end GlobalTheory.LlcSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitLocalComponentHasFixedVectorOfIsotypic
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.IsoTypFixLoc

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem rt_rt (h h' : GAf L n) (f : GAf L n → W) : NG.rt L n h (NG.rt L n h' f) = NG.rt L n (h * h') f := by
  funext g; simp [NG.rt, mul_assoc]

def LocEq (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T : τ.V →ₗ[ℂ] (GAf L n → W)) : Prop :=
  ∀ x : GAf L n, TrivOutside {s.v} x → ∀ a, T (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) a) = NG.rt L n x (T a)

theorem le_iSup_range (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) (hS : NG.IsIrrRep ρ S)
    (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T0 : τ.V →ₗ[ℂ] (GAf L n → W))
    (hT0inj : Function.Injective T0) (hT0S : ∀ a, T0 a ∈ S) (hT0eq : LocEq s τ i T0) :
    S ≤ ⨆ T : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}, LinearMap.range T.1 := by
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  have hnt : Nontrivial τ.V := by
    haveI := τ.irr
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
    have : ∀ W : Subrepresentation τ.ρ, W = ⊥ := by
      intro W
      ext x
      simp [Subsingleton.elim x 0]
    rw [this ⊤]
  let Good : (τ.V →ₗ[ℂ] (GAf L n → W)) → Prop := fun T => LocEq s τ i T ∧ ∀ u, T u ∈ S
  let Wd : Submodule ℂ (GAf L n → W) := ⨆ T : {T // Good T}, LinearMap.range T.1
  have hWdS : Wd ≤ S := by
    refine iSup_le fun T => ?_
    rintro _ ⟨u, rfl⟩
    exact T.2.2 u
  have hWdle : Wd ≤ ⨆ T : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}, LinearMap.range T.1 :=
    iSup_le fun T => le_iSup_of_le (⟨T.1, T.2.1⟩ : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}) le_rfl
  have htr : ∀ (T : τ.V →ₗ[ℂ] (GAf L n → W)) (y : GAf L n), Good T → TrivOutside {s.v}ᶜ y → Good ((NG.rt L n y).comp T) := by
    intro T y hT hy
    refine ⟨fun x hx u => ?_, fun u => hS.1.stable y _ (hT.2 u)⟩
    simp only [LinearMap.comp_apply]
    rw [hT.1 x hx u, rt_rt, rt_rt, (hcomm x y hx hy).eq]
  have hstab : ∀ h, ∀ f ∈ Wd, NG.rt L n h f ∈ Wd := by
    intro h f hf
    refine Submodule.iSup_induction _ (motive := fun f => NG.rt L n h f ∈ Wd) hf ?_ ?_ ?_
    · rintro T _ ⟨u, rfl⟩
      obtain ⟨x, y, hx, hy, he⟩ := hdec h
      have e : NG.rt L n h (T.1 u) = ((NG.rt L n y).comp T.1) (τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n x)) u) := by
        rw [LinearMap.comp_apply, T.2.1 x hx u, rt_rt, he, (hcomm x y hx hy).eq]
      rw [e]
      exact Submodule.mem_iSup_of_mem (⟨_, htr T.1 y T.2 hy⟩ : {T // Good T}) ⟨_, rfl⟩
    · simp
    · intro f₁ f₂ h₁ h₂; rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  have hT0 : Good T0 := ⟨hT0eq, hT0S⟩
  rcases hS.2.2 Wd ⟨hWdS.trans hS.1.le, hstab⟩ hWdS with h0 | h0
  · exfalso
    obtain ⟨u, hu⟩ := exists_ne (0 : τ.V)
    have hmem : T0 u ∈ Wd := Submodule.mem_iSup_of_mem (⟨T0, hT0⟩ : {T // Good T}) ⟨u, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact hu (hT0inj (hmem.trans (map_zero T0).symm))
  · rw [← h0]
    exact hWdle

theorem isoTyp_le (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W))
    (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (T0 : τ.V →ₗ[ℂ] (GAf L n → W))
    (hT0inj : Function.Injective T0) (hT0S : ∀ a, T0 a ∈ S) (hT0eq : LocEq s τ i T0) :
    NG.isoTyp ρ S ≤ ⨆ T : {T : τ.V →ₗ[ℂ] (GAf L n → W) // LocEq s τ i T}, LinearMap.range T.1 := by
  refine sSup_le ?_
  rintro S' ⟨hS', E, hE⟩
  let T1 : τ.V →ₗ[ℂ] (GAf L n → W) := S'.subtype ∘ₗ (E : S →ₗ[ℂ] S') ∘ₗ LinearMap.codRestrict S T0 hT0S
  refine le_iSup_range ρ S' hS' s τ i T1 ?_ (fun a => (E _).2) ?_
  · intro a b hab
    apply hT0inj
    have := E.injective (Subtype.ext hab)
    exact congrArg Subtype.val this
  · intro x hx a
    exact hE x ⟨T0 a, hT0S a⟩ ⟨_, hT0S _⟩ (hT0eq x hx a)

end GlobalTheory.IsoTypFixLoc

open GlobalTheory.IsoTypFixLoc in

theorem GlobalTheory.IsoTypFixLoc.main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (s : SplitPlace L) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s τ → ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous i → (∀ x : L, i (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ f ∈ NG.isoTyp ρ S, f ≠ 0 → (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, NG.rt L n κ f = f) → ∃ a : τ.V, a ≠ 0 ∧ ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, τ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (s.loc n κ)) a = a := by
  intro L _ _ _ n W _ _ ρ S hS s τ hloc i hi hiL f hf hf0 hfix
  classical
  obtain ⟨i', T0, hi', hi'L, hT0inj, hT0S, hT0eq⟩ := hloc
  obtain rfl := GlobalTheory.splitPlace_completion_equiv_unique L s i' i hi' hi hi'L hiL
  have hspan := isoTyp_le ρ S s τ i' T0 hT0inj hT0S hT0eq hf
  have hI := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  let H : Subgroup (GAf L n) :=
    { carrier := {x | TrivOutside {s.v} x}
      mul_mem' := fun hx hy => GlobalTheory.HeckeScalarSph.triv_mul hx hy
      one_mem' := GlobalTheory.HeckeScalarSph.triv_one
      inv_mem' := fun hx => GlobalTheory.HeckeScalarSph.triv_inv hx }
  let φ : H →* GL (Fin n) (s.w.adicCompletion L) :=
    (Matrix.GeneralLinearGroup.map i'.toRingHom).comp ((s.loc n).comp H.subtype)
  have hφ : Function.Surjective φ := by
    intro h
    obtain ⟨x, ⟨hx, e⟩, -⟩ := hI.2.2 (Matrix.GeneralLinearGroup.map i'.symm.toRingHom h)
    refine ⟨⟨x, hx⟩, ?_⟩
    change Matrix.GeneralLinearGroup.map i'.toRingHom (s.loc n x) = h
    rw [e]
    exact Units.ext (Matrix.ext fun a b => i'.apply_symm_apply _)
  let σ' : Representation ℂ H τ.V := τ.ρ.comp φ
  have hσ' : σ'.IsIrreducible := GlobalTheory.LocCompSplit.isIrreducible_comp_of_surjective τ.ρ φ hφ τ.irr
  let ρ' : Representation ℂ H (GAf L n → W) :=
    { toFun := fun x => NG.rt L n (x : GAf L n)
      map_one' := by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt]
      map_mul' := fun x y => by
        apply LinearMap.ext
        intro g
        funext a
        simp [NG.rt, mul_assoc] }
  rw [Submodule.mem_iSup_iff_exists_finset] at hspan
  obtain ⟨t, ht⟩ := hspan
  let T : t → σ'.IntertwiningMap ρ' := fun j =>
    ⟨j.1.1, fun g => LinearMap.ext fun a => j.1.2 g.1 g.2 a⟩
  have hf' : f ∈ ⨆ j, LinearMap.range (T j).toLinearMap := by
    rw [iSup_subtype'] at ht
    exact ht
  let K : Subgroup H := (GlobalTheory.HeckeScalarSph.locK n s.v).comap H.subtype
  have hfixK : ∀ k ∈ K, ρ' k f = f := fun k hk => hfix k.1 hk
  have hne := GlobalTheory.UnrLoc.fixed_ne_bot_of_mem_iSup_range hσ' T K hf' hf0 hfixK
  rw [Submodule.ne_bot_iff] at hne
  obtain ⟨y, hy, hy0⟩ := hne
  refine ⟨y, hy0, fun κ hκ => ?_⟩
  exact (GlobalTheory.Parabolic.mem_fixed.1 hy) ⟨κ, hκ.2⟩ hκ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceIdempotentMulEqSelfOfSupported
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.PlaceSupp

theorem tensCast_tmul_one {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (v : HeightOneSpectrum (𝓞 F1)) (α : FiniteAdeleRing (𝓞 F1) F1) (h1 : α v = 1) (h0 : ∀ v', v' ≠ v → α v' = 0) :
    ∃ (w : HeightOneSpectrum (𝓞 F2)) (α' : FiniteAdeleRing (𝓞 F2) F2),
      GlobalTheory.NJoin.tensCast h (α ⊗ₜ[F1] (1 : E)) = (1 : E) ⊗ₜ[F2] α' ∧ α' w = 1 ∧ ∀ v', v' ≠ w → α' v' = 0 := by
  subst h
  exact ⟨v, α, rfl, h1, h0⟩

open Classical in

theorem equivFinsuppOfBasisRight_rTensor {K M N N' ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup N'] [Module K N']
    (b : Module.Basis ι K M) (f : N →ₗ[K] N') (x : N ⊗[K] M) (i : ι) :
    TensorProduct.equivFinsuppOfBasisRight b (LinearMap.rTensor M f x) i =
      f (TensorProduct.equivFinsuppOfBasisRight b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul m n => simp [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem rTensor_eq_zero {K M N P Q ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]
    (b : Module.Basis ι K M) (f : N →ₗ[K] P) (g : N →ₗ[K] Q) (hfg : ∀ n, f n = 0 → g n = 0 → n = 0)
    (x : N ⊗[K] M) (h1 : LinearMap.rTensor M f x = 0) (h2 : LinearMap.rTensor M g x = 0) : x = 0 := by
  classical
  let e := TensorProduct.equivFinsuppOfBasisRight (M := N) b
  have hc : ∀ i, e x i = 0 := by
    intro i
    apply hfg
    · have := equivFinsuppOfBasisRight_rTensor b f x i
      rw [h1, map_zero, Finsupp.zero_apply] at this
      exact this.symm
    · have := equivFinsuppOfBasisRight_rTensor b g x i
      rw [h2, map_zero, Finsupp.zero_apply] at this
      exact this.symm
  have : e x = 0 := Finsupp.ext hc
  simpa using congrArg e.symm this

theorem AE_eq_zero (D : D7) (x : Formalism.L2.Theta.AE D) (h1 : Formalism.L2.Theta.infPart D x = 0)
    (h2 : Formalism.L2.Theta.finPart D x = 0) : x = 0 := by
  classical
  let b := Module.finBasis D.host.F D.host.E
  refine rTensor_eq_zero b (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA D.host.F).toLinearMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F).toLinearMap
    (fun n hf hs => Prod.ext hf hs) x ?_ ?_
  · rw [← h1]; clear h1 h2
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => rfl
    | add x y hx hy => rw [LinearMap.map_add, RingHom.map_add, hx, hy]
  · rw [← h2]; clear h1 h2
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => rfl
    | add x y hx hy => rw [LinearMap.map_add, RingHom.map_add, hx, hy]

set_option maxHeartbeats 2000000 in

theorem idem_mul_eq_self : ∀ (D : D7) (s : SplitPlace D.host.E) (hF : D.host.F = maximalRealSubfield D.host.E) (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E), (∀ a : Formalism.L2.Theta.AE D, p.π a = c (s.proj (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)))) → ∀ a : Formalism.L2.Theta.AE D, Formalism.L2.Theta.infPart D a = 0 → (∀ v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), v' ≠ s.v → ReciprocityTheory.Aut.compAt D.host.E v' (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D a)) = 0) → (p.e + Formalism.L2.Theta.cA D p.e) * a = a := by
  intro D s hF p c hπ a ha0 haf
  obtain ⟨he2, hec, v, ε, ⟨α, rfl, hα1, hα0⟩, hsum⟩ := p.split
  rw [hsum]
  have hι1 : p.ι 1 = p.e := by
    have := p.ι_π 1
    rwa [map_one, mul_one] at this
  have hπe : p.π p.e = 1 := by rw [← hι1, p.π_ι]
  have hee : p.e * algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α) = p.e := by
    rw [← hsum, mul_add, he2, hec, add_zero]
  have hfin : Formalism.L2.Theta.finPart D (algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D)
      (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α)) = α ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  obtain ⟨w, α', hT, hw1, hw0⟩ := tensCast_tmul_one hF v α hα1 hα0
  have hws : w = s.v := by
    by_contra hne
    have h0 : α' s.v = 0 := hw0 s.v (Ne.symm hne)
    have hz : p.π (algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α)) = 0 := by
      rw [hπ, hfin, hT]
      have : s.proj ((1 : D.host.E) ⊗ₜ α') = 0 := by
        rw [SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        exact h0
      rw [this, map_zero]
    have := congrArg p.π hee
    rw [map_mul, hz, mul_zero, hπe] at this
    exact zero_ne_one this
  subst hws
  set x := algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) (Formalism.L2.Theta.AE D) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 α) with hx
  suffices hb : x * a - a = 0 from sub_eq_zero.mp hb
  apply AE_eq_zero D
  · rw [RingHom.map_sub, RingHom.map_mul, ha0, mul_zero, sub_zero]
  · have key : GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D (x * a - a)) = 0 := by
      apply GlobalTheory.AL_eq_zero_of_compAt
      intro v''
      rw [(Formalism.L2.Theta.finPart D).map_sub, (Formalism.L2.Theta.finPart D).map_mul, (GlobalTheory.NJoin.tensCast hF).map_sub,
        (GlobalTheory.NJoin.tensCast hF).map_mul, (compAt D.host.E v'').map_sub, (compAt D.host.E v'').map_mul, hfin, hT]
      by_cases hv : v'' = s.v
      · subst hv
        have : compAt D.host.E s.v ((1 : D.host.E) ⊗ₜ α') = 1 := by
          rw [compAt, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
          change (1 : D.host.E) ⊗ₜ (α' s.v) = 1
          rw [hw1]
          rfl
        rw [this, one_mul, sub_self]
      · rw [haf v'' hv, mul_zero, sub_zero]
    exact (GlobalTheory.NJoin.tensCast hF).map_eq_zero_iff.mp key

end GlobalTheory.PlaceSupp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilityThird
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigStr

theorem sysParam_split : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ s : GlobalTheory.DownLift.Sys D, GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i)) → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ Bw, GlobalTheory.LFun.IsSysParam D.sp.cm.sig (Formalism.IndefR.Links.Vc D j).rank (rfl : w.under (𝓞 D.host.F) = _) (s w) Bw := by
  intro _ hL D P X _ _ _ _ i hμ j hj x _ f _ y _ hy0 h hh s hy w hw _
  obtain ⟨B, hB⟩ := GlobalTheory.DownLift.Params.paramsV X.R X.given.core j (X.tupT (D.nd.mu i)) h hh s y hy hy0
  exact ⟨B w, hB _ hw w rfl⟩

end GlobalTheory.EigStr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeNonzeroRecursionOfEigen
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TypeNZJoin

open Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.RecTie

set_option maxHeartbeats 1000000 in

theorem inj_at {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (hT : ∀ j t, GlobalTheory.DownLift.TypeNZ X.R j t) (i : D.nd.Loc) (hS : GlobalTheory.NJoin.EigString X i)
    (hG : GlobalTheory.NJoin.EigGood X i) (hμ : Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (x : D.nd.X i) (hx : x ∈ ZgoodN D.nd D.naut i) (f : D.what₂.Mt (D.nd.mu i) (j.1 + 1))
    (hf : (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x)
    (h0 : D.what₂.thetaP (D.nd.mu i) (j.1 + 1) f = 0) : f = 0 := by
  have hC := X.given.core
  have hfm := (X.IL.jMt _ hμ j f).2
  obtain ⟨y, hy⟩ : ∃ y, (LinearEquiv.ofInjective _ (X.hinj j (X.tupT (D.nd.mu i)))).symm
      ⟨((X.IL.jMt _ hμ j f).1 : Formalism.L2.Theta.GA D (Vc D j) → (X.R.cV j).W), hfm.1⟩ = y := ⟨_, rfl⟩
  have hyf : X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f := by
    rw [← hy]
    exact congrArg Subtype.val ((LinearEquiv.ofInjective _ (X.hinj j (X.tupT (D.nd.mu i)))).apply_symm_apply _)
  have hthG : X.R.thG j (X.tupT (D.nd.mu i)) y = 0 := by
    have hM := GlobalTheory.ThetaLevelP.thF_mem_level X.R X.F hC.lev hC.models hC.thP X.R.hv0 false j (X.tupT (D.nd.mu i)) y
      (by rw [hyf]; exact hfm.2)
    obtain ⟨w, hw1, hw2, hw3⟩ := X.fire.2.1 (D.nd.mu i) hμ j f
    have hw' : PiTensorProduct.lift (X.R.thF j (X.tupT (D.nd.mu i)) y) ∘ₗ
        (toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj).embK j =
        (toLiftReal X.R X.F X.tupT X.hm X.hTop X.hinj).thC _ j (X.IL.jMt _ hμ j f) := by
      rw [← hy]; rfl
    have hwe : w = PiTensorProduct.lift (X.R.thF j (X.tupT (D.nd.mu i)) y) := by
      refine sub_eq_zero.1 (X.fire.2.2 j _ (sub_mem hw1 (Submodule.mem_map_of_mem hM)) ?_)
      exact (LinearMap.sub_comp _ _ _).trans (by rw [hw2]; exact sub_eq_zero.2 hw'.symm)
    have hth := X.recR.tied.lift.theta (D.nd.mu i) hμ j f w (X.fire.1 _ hμ j) hw1 hw2 hw3
    rw [h0, map_zero, ZeroMemClass.coe_zero, hwe] at hth
    have h2 : PiTensorProduct.lift (postOn _ (X.R.eWf j (sg0 D X.A)) (X.R.thF j (X.tupT (D.nd.mu i)) y)) = 0 := by
      rw [GlobalTheory.ThetaFireLift.lift_postOn]; exact hth.symm
    have h3 : (X.R.HW j (sg0 D X.A)).e (X.R.thG j (X.tupT (D.nd.mu i)) y) = 0 := by
      rw [hC.thP.thG]; exact (LinearEquiv.map_eq_zero_iff _).1 h2
    exact (hC.models.HW j _).1 (h3.trans (map_zero _).symm)
  have hy0 : y = 0 := by
    by_contra hne
    obtain ⟨h, hh⟩ := GlobalTheory.LiftOntoCompare.exists_opsV hC.lev hC.models j (X.tupT (D.nd.mu i))
    obtain ⟨s, hs1, hs2⟩ := hS hμ j hj x hx f hf y hyf hne h hh
    exact hne (hT j _ h hh s hs1 y hs2 (hG hμ j hj x hx f hf y hyf) hthG)
  have h4 : X.IL.jMt _ hμ j f = 0 := by
    apply Subtype.ext
    show X.fn hμ j f = 0
    rw [← hyf, hy0, map_zero]
  exact (LinearEquiv.map_eq_zero_iff _).1 h4

theorem of_cast {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (S : Submodule ℂ (D.what₂.Mt μ b))
    (H : ∀ f : D.what₂.Mt μ a, (h ▸ f : D.what₂.Mt μ b) ∈ S → D.what₂.thetaP μ a f = 0 → f = 0) :
    ∀ F ∈ S, D.what₂.thetaP μ b F = 0 → F = 0 := by
  subst h
  exact H

theorem typeNZRec_of_join : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D),
    ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), (∀ j t, GlobalTheory.DownLift.TypeNZ X.R j t) →
    ∀ i, GlobalTheory.NJoin.EigString X i → GlobalTheory.NJoin.EigGood X i → GlobalTheory.RowCopy.TypeNZRec D.nd D.naut i := by
  intro hL D P X _ hT i hS hG x hx
  have hμ : Used0 D (D.nd.mu i) :=
    Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩
  have hr := D.nd.j_range i
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i := ⟨⟨D.nd.j i - 1, by omega⟩, by simp only; omega⟩
  exact of_cast hj _ fun f hf h0 => inj_at X hT i hS hG hμ j hj x hx f hf h0

end GlobalTheory.TypeNZJoin
end
end

