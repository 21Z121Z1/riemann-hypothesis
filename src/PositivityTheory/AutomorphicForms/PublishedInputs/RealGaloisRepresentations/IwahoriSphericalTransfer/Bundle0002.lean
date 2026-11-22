import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0046
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0034
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsFurther
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeMultOne

theorem main : ∀ (F : Type) [Field F] [NumberField F] (η η' : HChar F), (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, η.UnrAt v ∧ η'.UnrAt v ∧ η.val v = η'.val v) → η = η' := by
  intro F _ _ η η' h
  set S : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.mp h).toFinset with hS
  have key : η * η'⁻¹ = 1 := by
    refine Subtype.ext (GlobalTheory.FrobDense.eq_one_of_away (η * η'⁻¹).1 (η * η'⁻¹).2.1 (η * η'⁻¹).2.2 S fun v hv => ?_)
    have hv' : η.UnrAt v ∧ η'.UnrAt v ∧ η.val v = η'.val v := by
      by_contra hc
      exact hv (by rw [hS, Set.Finite.mem_toFinset]; exact hc)
    obtain ⟨h1, h2, h3⟩ := hv'
    intro x
    refine GlobalTheory.FrobDense.eq_one_of_unif ((η * η'⁻¹).loc v) (fun y hy => ?_) x
    rw [HChar.loc_mul, HChar.loc_inv, η.val_eq h1 y hy, η'.val_eq h2 y hy, h3, mul_inv_cancel]
  exact mul_inv_eq_one.mp key

end GlobalTheory.HeckeMultOne
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsRest
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.TemperedTransport.main : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (h' : IsPlaceOver A w) (j : F →+* K) (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) j i → ∀ (x : WD h) (x' : WD h'), WDRel (RingEquiv.refl Ω) x x' → ∀ s : ℝ, (x'.lpTw s).tempered → (x.lpTw s).tempered := by
  intro F Ω _ _ _ _ _ K _ _ _ _ A v w h h' j i hP x x' hx s ht
  obtain ⟨S, hS, -, -, -, -, hTw, -⟩ :=
    GlobalTheory.T.place_over_transport_ring_iso_symm F Ω A v h K Ω A w h' (RingEquiv.refl Ω) j i hP
  obtain ⟨c, hc, hdeg, hq, -⟩ :=
    GlobalTheory.T.place_over_transport_ring_iso F Ω A v h K Ω A w h' (RingEquiv.refl Ω) j i hP
  have hx2 : WDRel (RingEquiv.refl Ω) (x.lpTw s) (x'.lpTw s) := by
    rw [hS, hTw, (hS x x').mp hx]
  obtain ⟨n, b, b', hb, hb', hN, hρ⟩ := hx2
  rw [← hb, WD.tempered_mk]
  rw [← hb', WD.tempered_mk] at ht
  intro φ hφ
  have h1 : b.ρ φ = b'.ρ (c φ) := hρ φ (c φ) ((hc φ (c φ)).mpr rfl)
  have h2 := ht (c φ) (by rw [hdeg, hφ])
  rw [h1, hN, ← hq]
  exact h2
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsTer
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TraceConj

theorem main : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ) (r r' : Γ →* GL (Fin n) k), IsSSRep r → IsSSRep r' → (∀ s, ((r s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = ((r' s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → RepIso r r' := by
  intro Γ k _ _ _ n r r' hr hr' htr
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hr hr' (fun g => by
    refine GlobalTheory.QuadKernelConj.charpoly_eq_of_trace_pow _ _ fun m => ?_
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
    exact htr (g ^ m))
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩

end GlobalTheory.TraceConj
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.InducedEmbeddingExtends
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem induced_embedding_extends : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (Bw' : LocBridge l K Ω (Dec (F := K) A) O), Bw'.Kw = Bw.Kw → Bw'.j = Bw.j → ∀ (τ : F →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' → ∃ (τK : K →+* Qbar l) (τ'' : ↥Bw'.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), τK.comp (algebraMap F K) = τ ∧ IsInduced Bw' τK τ'' := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ l _ A O _ _ _ Bw Bw' hK hj τ LL' τ' hτ
  obtain ⟨Kw', j', j_E', _, _, _, _, _, _, _, _, _, _, _⟩ := Bw'
  dsimp only at hK hj ⊢
  subst hK
  subst hj
  let ι : K →+* ↥Bw.Kw.1 :=
    { toFun := fun x => ⟨Bw.j (algebraMap K Ω x), j_E' x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  refine ⟨(LL'.1.val.toRingHom.comp (τ'.toRingHom.comp ι)), τ', ?_, ?_⟩
  · ext x
    have := hτ x
    simp only [RingHom.coe_comp, Function.comp_apply] at this ⊢
    rw [this]
    have e : (ι (algebraMap F K x)) = ⟨Bw.j (algebraMap F Ω x), Bw.j_E x⟩ := by
      apply Subtype.ext
      simp [ι, ← IsScalarTower.algebraMap_apply]
    simp [e]
  · intro x
    rfl

end GlobalTheory
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.InfinitePrimesNegIsSquare
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGal.PrimesNegSquare

open Polynomial

theorem isSquare_neg_of_dvd (q : ℕ) [Fact q.Prime] (p : ℕ) (h : ((8 * q : ℕ) : ℤ) ∣ (p : ℤ) + 1) :
    IsSquare (-(p : ℚ_[q])) := by
  obtain ⟨c, hc⟩ := h
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
  have h2pos : 0 < ‖(2 : ℤ_[q])‖ := norm_pos_iff.mpr two_ne_zero
  have h2le : ‖(2 : ℤ_[q])‖ ≤ 1 := PadicInt.norm_le_one _
  have hcle : ‖((c : ℤ) : ℤ_[q])‖ ≤ 1 := PadicInt.norm_le_one _
  have hqn : ‖((q : ℕ) : ℤ_[q])‖ = (q : ℝ)⁻¹ := PadicInt.norm_p
  have key : ‖(((p : ℤ) + 1 : ℤ) : ℤ_[q])‖ < ‖(2 : ℤ_[q])‖ ^ 2 := by
    rw [hc]
    push_cast
    have e8 : (8 : ℤ_[q]) = 2 ^ 3 := by norm_num
    rw [e8, norm_mul, norm_mul, norm_pow, hqn]
    have hqinv : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
    have hqinv0 : 0 < (q : ℝ)⁻¹ := by positivity
    calc ‖(2 : ℤ_[q])‖ ^ 3 * (q : ℝ)⁻¹ * ‖((c : ℤ) : ℤ_[q])‖
        ≤ ‖(2 : ℤ_[q])‖ ^ 3 * (q : ℝ)⁻¹ := by
          apply mul_le_of_le_one_right (by positivity) hcle
      _ < ‖(2 : ℤ_[q])‖ ^ 2 * 1 := by
          rw [pow_succ, mul_assoc]
          apply mul_lt_mul_of_pos_left _ (by positivity)
          calc ‖(2 : ℤ_[q])‖ * (q : ℝ)⁻¹ ≤ 1 * (q : ℝ)⁻¹ := by gcongr
            _ < 1 := by simpa using hqinv
      _ = ‖(2 : ℤ_[q])‖ ^ 2 := mul_one _
  let F : ℤ[X] := X ^ 2 + C (p : ℤ)
  have hF : ‖aeval (1 : ℤ_[q]) F‖ < ‖aeval (1 : ℤ_[q]) (derivative F)‖ ^ 2 := by
    have e1 : aeval (1 : ℤ_[q]) F = (((p : ℤ) + 1 : ℤ) : ℤ_[q]) := by
      simp [F]; ring
    have e2 : aeval (1 : ℤ_[q]) (derivative F) = 2 := by
      simp [F]
      exact map_ofNat _ 2
    rw [e1, e2]; exact key
  obtain ⟨z, hz, -⟩ := hensels_lemma hF
  have hz' : z ^ 2 + (p : ℤ_[q]) = 0 := by simpa [F] using hz
  refine ⟨(z : ℚ_[q]), ?_⟩
  have : ((z ^ 2 + (p : ℤ_[q]) : ℤ_[q]) : ℚ_[q]) = 0 := by rw [hz']; simp
  push_cast at this
  linear_combination -this

theorem infinite_primes_neg_isSquare : ∀ (q : ℕ) [Fact q.Prime], {p : ℕ | p.Prime ∧ IsSquare (-(p : ℚ_[q]))}.Infinite := by
  intro q _
  have hq0 : (8 * q) ≠ 0 := by
    have := (Fact.out : q.Prime).pos; omega
  haveI : NeZero (8 * q) := ⟨hq0⟩
  have hu : IsUnit (-1 : ZMod (8 * q)) := isUnit_one.neg
  refine (Nat.infinite_setOfPred_prime_and_eq_mod hu).mono ?_
  rintro p ⟨hp, hpe⟩
  refine ⟨hp, GlobalTheory.RealGal.PrimesNegSquare.isSquare_neg_of_dvd q p ?_⟩
  have : (((p : ℤ) + 1 : ℤ) : ZMod (8 * q)) = 0 := by
    push_cast; rw [hpe]; ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this

end GlobalTheory.RealGal.PrimesNegSquare
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.IsoComm
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocCompCLit

open Matrix

section

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

private theorem iso_comm (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (T : Module.End ℂ V)
    (hT : ∀ g x, T (ρ g x) = ρ g (T x)) {x : V}
    (hx : x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) :
    T x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 := by
  refine Submodule.mem_comap.1 ((iSup_le (fun f => ?_) : _ ≤ Submodule.comap T _) hx)
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by simp only [LinearMap.comp_apply, f.2, hT]⟩ ⟨v, rfl⟩

private theorem iso_act (σ : Representation ℂ G W) (ρ : Representation ℂ G V) (g : G) {x : V}
    (hx : x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) :
    ρ g x ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1 := by
  refine Submodule.mem_comap.1 ((iSup_le (fun f => ?_) : _ ≤ Submodule.comap (ρ g) _) hx)
  rintro _ ⟨v, rfl⟩
  exact Submodule.mem_iSup_of_mem f ⟨σ g v, f.2 g v⟩

end

theorem main : GlobalTheory.Mem.LiteralAutomorphy.LitN → LocCompC := by
  intro H E _ _ _ a π w
  refine ⟨(LocEx.exists_isLocComp H.aut.fin E a π w).imp fun _ h => h.1, fun σ hσ => ?_⟩
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne_bot, ?_⟩
  obtain ⟨f, h0, hf⟩ := hσ
  change ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 = ⊤
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  have hop : ∀ (o : Op E a) (x : π.V),
      x ∈ (⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1) →
      π.op o x ∈ ⨆ f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)}, LinearMap.range f.1 := by
    intro o x hx
    cases o with
    | fin k =>
      have h1 := iso_act σ.ρ (π.locRep w) (GeneralLinearGroup.map (pLoc E w) k) (iso_comm σ.ρ (π.locRep w)
        (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k)) (fun g' y => by
        simp only [CuspSub.locRep, MonoidHom.comp_apply]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
          LocUniq.comm_locGL w (LocEx.map_pLoc_inv_mul w k)]) hx)
      have e : π.locRep w (GeneralLinearGroup.map (pLoc E w) k)
          (π.finPart ((locGL E a w (GeneralLinearGroup.map (pLoc E w) k))⁻¹ * k) x) = π.op (.fin k) x := by
        rw [CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
        rfl
      rwa [e] at h1
    | cpt k =>
      refine iso_comm _ _ _ (fun g y => Subtype.ext ?_) hx
      change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
        (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
      rw [← map_mul, ← map_mul, infGL_comm]
    | lie X =>
      refine iso_comm _ _ _ (fun g y => Subtype.ext ?_) hx
      exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1
  rcases π.irred (Submodule.map π.V.subtype _) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩) with h1 | h1
  · have h2 := hi (h1.trans (Submodule.map_bot _).symm)
    exact absurd (LinearMap.range_eq_bot.1 (le_bot_iff.1 (h2 ▸ le_iSup
      (fun f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)} => LinearMap.range f.1) ⟨f, hf⟩))) h0
  · exact hi (h1.trans (Submodule.map_subtype_top _).symm)

end GlobalTheory.LocCompCLit
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.IwahoriSphericalTransfer
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompletionIso

open ValuativeRel

section Val

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem valuation_le_one_of_map (f : k ≃+* k') (hf : Continuous f) {x : k}
    (hx : valuation k' (f x) ≤ 1) : valuation k x ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have hx0 : x ≠ 0 := by rintro rfl; simp at h
  have h1 : valuation k x⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ h
  have h2 := GlobalTheory.TypeRec.TwistInert.valuation_lt_one_map f.toRingHom hf h1
  have hfx : f x ≠ 0 := (map_ne_zero f).2 hx0
  have hw : 0 < valuation k' (f x) := by rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 hfx
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, map_inv₀] at h2
  exact absurd ((inv_lt_one₀ hw).1 h2) (not_lt.2 hx)

theorem valuation_lt_one_of_map (f : k ≃+* k') (hf : Continuous f) {x : k}
    (hx : valuation k' (f x) < 1) : valuation k x < 1 := by
  by_contra h
  rw [not_lt] at h
  have hx0 : x ≠ 0 := by rintro rfl; simp at h
  have h1 : x⁻¹ ∈ 𝒪[k] := by
    rw [Valuation.mem_integer_iff, map_inv₀]; exact inv_le_one_of_one_le₀ h
  have h2 := GlobalTheory.LastCompare.map_mem_integer f.toMonoidHom hf h1
  rw [Valuation.mem_integer_iff] at h2
  have hfx : f x ≠ 0 := (map_ne_zero f).2 hx0
  have hw : 0 < valuation k' (f x) := by rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 hfx
  have h3 : valuation k' (f x⁻¹) ≤ 1 := h2
  rw [map_inv₀, map_inv₀] at h3
  exact absurd hx (not_lt.2 ((inv_le_one₀ hw).1 h3))

variable (f : k ≃+* k') (hf : Continuous f) {n : Type} [Fintype n] [DecidableEq n]

theorem map_map_symm (h : GL n k') :
    Matrix.GeneralLinearGroup.map f.toRingHom (Matrix.GeneralLinearGroup.map f.symm.toRingHom h) = h := by
  ext a b
  simp

include hf in

theorem map_symm_mem_KO {h : GL n k'} (hh : h ∈ GlobalTheory.SplitWeil.KO k' n) :
    Matrix.GeneralLinearGroup.map f.symm.toRingHom h ∈ GlobalTheory.SplitWeil.KO k n := by
  obtain ⟨h0, rfl⟩ := hh
  let j : 𝒪[k'] →+* 𝒪[k] := (f.symm.toRingHom.comp (algebraMap 𝒪[k'] k')).codRestrict 𝒪[k] (fun y => by
      show valuation k (f.symm (y : k')) ≤ 1
      apply valuation_le_one_of_map f hf
      rw [RingEquiv.apply_symm_apply]
      exact y.2)
  refine ⟨Matrix.GeneralLinearGroup.map j h0, ?_⟩
  ext a b
  simp [j] <;> rfl

include hf in

theorem map_symm_mem_iwahori [LinearOrder n] {h : GL n k'} (hh : h ∈ GlobalTheory.SmGL.iwahori k' n) :
    Matrix.GeneralLinearGroup.map f.symm.toRingHom h ∈ GlobalTheory.SmGL.iwahori k n := by
  rw [GlobalTheory.SmGL.mem_iwahori] at hh ⊢
  refine ⟨map_symm_mem_KO f hf hh.1, fun a b hab => ?_⟩
  apply valuation_lt_one_of_map f hf
  have := hh.2 a b hab
  simpa using this

end Val

theorem fixed_ne_bot_transfer {G G' V V' : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (ρ : Representation ℂ G V) (ρ' : Representation ℂ G' V') (φ : G →* G')
    (ψ : G' → G) (hψ : ∀ g, φ (ψ g) = g) (e : V ≃ₗ[ℂ] V') (he : ∀ g x, e (ρ g x) = ρ' (φ g) (e x))
    (H : Subgroup G) (H' : Subgroup G') (hH : ∀ h ∈ H', ψ h ∈ H) :
    GlobalTheory.PRep.fixed ρ H ≠ ⊥ → GlobalTheory.PRep.fixed ρ' H' ≠ ⊥ := by
  intro hne
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hx' : ∀ h : H, ρ (h : G) x = (((1 : H →* ℂˣ) h : ℂˣ) : ℂ) • x := hx
  refine (Submodule.ne_bot_iff _).2 ⟨e x, ?_, by simpa using hx0⟩
  show ∀ h : H', ρ' (h : G') (e x) = (((1 : H' →* ℂˣ) h : ℂˣ) : ℂ) • e x
  intro h
  have h1 := hx' ⟨ψ h, hH h h.2⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
  rw [← hψ h, ← he, h1]

theorem iwahori_spherical_transfer : ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) (i : v.adicCompletion F ≃+* w.adicCompletion K), Continuous i → ∀ (a : ℕ) (σ : SmIrr (GL (Fin a) (v.adicCompletion F))) (σ' : SmIrr (GL (Fin a) (w.adicCompletion K))) (e : σ.V ≃ₗ[ℂ] σ'.V), (∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)) → (GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SmGL.iwahori (v.adicCompletion F) (Fin a)) ≠ ⊥ → GlobalTheory.PRep.fixed σ'.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion K) (Fin a)) ≠ ⊥) ∧ (GlobalTheory.SmGL.IsSpherical σ.ρ → GlobalTheory.SmGL.IsSpherical σ'.ρ) := by
  intro F K _ _ _ _ v w i hi a σ σ' e he
  exact ⟨fixed_ne_bot_transfer σ.ρ σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom)
      (Matrix.GeneralLinearGroup.map i.symm.toRingHom) (map_map_symm i) e he _ _
      (fun h hh => map_symm_mem_iwahori i hi hh),
    fixed_ne_bot_transfer σ.ρ σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom)
      (Matrix.GeneralLinearGroup.map i.symm.toRingHom) (map_map_symm i) e he _ _
      (fun h hh => map_symm_mem_KO i hi hh)⟩

end GlobalTheory.CompletionIso
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.NormVUnderPow
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AttResTower

theorem normV_under_pow {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

theorem two_le_normV {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ normV v := by
  show 2 ≤ Ideal.absNorm v.asIdeal
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem under_under {F K M : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra F K] [Algebra F M] [Algebra K M] [IsScalarTower F K M] (w : HeightOneSpectrum (𝓞 M)) :
    (w.under (𝓞 K)).under (𝓞 F) = w.under (𝓞 F) := by
  apply HeightOneSpectrum.ext
  show Ideal.comap _ (Ideal.comap _ w.asIdeal) = Ideal.comap _ w.asIdeal
  rw [Ideal.comap_comap]
  congr 1
  ext x
  first
  | exact (IsScalarTower.algebraMap_eq (𝓞 F) (𝓞 K) (𝓞 M)).symm ▸ rfl
  | (apply RingOfIntegers.coe_injective; simp only [RingHom.comp_apply, RingOfIntegers.algebraMap_coe]; exact (IsScalarTower.algebraMap_apply F K M (x : F)).symm)
  | (apply RingOfIntegers.ext; simp [IsScalarTower.algebraMap_apply F K M])

end GlobalTheory.AttResTower

theorem GlobalTheory.AttResTower.attRes_comp_res : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [Algebra F M] [Algebra M Ω] [IsScalarTower F M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower F K M] [IsScalarTower K M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r : G K Ω →* GL (Fin a) (Qbar l)), AttRes π ι K r → AttRes π ι M (r.comp (res K Ω M)) := by
  intro F Ω _ _ _ _ _ _ K _ _ _ _ _ _ M _ _ _ _ _ _ _ _ _ l _ ι a π r hatt
  unfold AttRes at hatt ⊢
  filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually hatt] with w h f hf
  have huv := GlobalTheory.AttResTower.under_under (F := F) (K := K) w
  have h1 := GlobalTheory.AttResTower.normV_under_pow (K := F) (w.under (𝓞 K))
  have h2 := GlobalTheory.AttResTower.normV_under_pow (K := K) w
  obtain ⟨B, hB, hF⟩ := h _ h1
  rw [huv] at hB hF h1
  refine ⟨B, hB, ?_⟩
  have h3 := (UpperTheory.frobenius_power_compatibility K M Ω l ι w _ h2).1 a r _ hF
  have hff : f = (w.under (𝓞 K)).asIdeal.inertiaDeg (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 K) := by
    apply Nat.pow_right_injective (GlobalTheory.AttResTower.two_le_normV (w.under (𝓞 F)))
    simp only
    rw [← hf, h2, h1, ← pow_mul]
  rw [Multiset.map_map] at h3
  rw [hff]
  convert h3 using 2
  simp [Function.comp_def, pow_mul]
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.SymmMultisetCentreUnique
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Glob

theorem symm_multiset_centre_unique : ∀ (s : Multiset ℤ) (x y : ℤ), s ≠ 0 → s = s.map (x - ·) → s = s.map (y - ·) → x = y := by
  intro s x y hs hx hy
  have key : ∀ z : ℤ, s = s.map (z - ·) → 2 * s.sum = (Multiset.card s : ℤ) * z := by
    intro z hz
    have h1 : (s.map (z - ·)).sum = (Multiset.card s : ℤ) * z - s.sum := by
      rw [Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, Multiset.map_id']
      simp [nsmul_eq_mul]
    have h2 : s.sum = (Multiset.card s : ℤ) * z - s.sum := by
      conv_lhs => rw [hz]
      exact h1
    linarith
  have hc : (Multiset.card s : ℤ) ≠ 0 := by
    exact_mod_cast (mt Multiset.card_eq_zero.mp hs)
  have := (key x hx).symm.trans (key y hy)
  exact mul_left_cancel₀ hc this

end GlobalTheory.Glob
end

