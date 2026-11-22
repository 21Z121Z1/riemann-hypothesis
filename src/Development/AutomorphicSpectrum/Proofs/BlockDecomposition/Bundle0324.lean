import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0287
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0319
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0286
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0285
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0318
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0320
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0014
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGradedMapGlueD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0314
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0315
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0021
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0303
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0312
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0316
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0317

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationUniqueSubquotient
section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Filtration

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ G V} {σ : Representation ℂ G W}

noncomputable def descend (f : π.IntertwiningMap σ) (B A : Subrepresentation π)
    (h : ∀ v ∈ A.toSubmodule, f v = 0) : (subQuot B A).IntertwiningMap σ where
  toLinearMap := Submodule.liftQ _ (f.toLinearMap ∘ₗ B.toSubmodule.subtype) (fun v hv => h v.1 hv)
  isIntertwining' g := by
    apply Submodule.linearMap_qext
    ext v
    exact f.isIntertwining _ _ g v.1

theorem vanish_step (f : π.IntertwiningMap σ) {A B : Subrepresentation π}
    (hA : ∀ v ∈ A.toSubmodule, f v = 0)
    (hz : ∀ φ : (subQuot B A).IntertwiningMap σ, φ.toLinearMap = 0) :
    ∀ v ∈ B.toSubmodule, f v = 0 := by
  intro v hv
  have h1 := LinearMap.congr_fun (hz (GlobalTheory.CompanionTheory.Filtration.descend f B A hA)) (Submodule.Quotient.mk ⟨v, hv⟩)
  have h2 : (GlobalTheory.CompanionTheory.Filtration.descend f B A hA).toLinearMap (Submodule.Quotient.mk ⟨v, hv⟩) = f v := by
    first
      | rfl
      | simp [GlobalTheory.CompanionTheory.Filtration.descend, Submodule.liftQ_apply]
  rw [← h2, h1, LinearMap.zero_apply]

theorem vanish_climb {N : ℕ} (S : Fin (N + 1) → Subrepresentation π) (f : π.IntertwiningMap σ)
    (lo : ℕ) (hlo : lo < N + 1)
    (h0 : ∀ v ∈ (S ⟨lo, hlo⟩).toSubmodule, f v = 0) (hi : ℕ) (hle : lo ≤ hi) :
    ∀ (hhi : hi < N + 1),
      (∀ t : Fin N, lo ≤ t.val → t.val < hi →
        ∀ φ : (subQuot (S t.succ) (S t.castSucc)).IntertwiningMap σ, φ.toLinearMap = 0) →
      ∀ v ∈ (S ⟨hi, hhi⟩).toSubmodule, f v = 0 := by
  induction hi, hle using Nat.le_induction with
  | base =>
    intro _ _
    exact h0
  | succ k hk ih =>
    intro hhi hz
    have hkN : k < N := Nat.lt_of_succ_lt_succ hhi
    have ih' := ih (Nat.lt_succ_of_lt hkN)
      (fun t h1 h2 => hz t h1 (Nat.lt_succ_of_lt h2))
    exact GlobalTheory.CompanionTheory.Filtration.vanish_step f
      (A := S (⟨k, hkN⟩ : Fin N).castSucc) (B := S (⟨k, hkN⟩ : Fin N).succ) ih'
      (hz ⟨k, hkN⟩ hk (Nat.lt_succ_self k))

theorem intertwining_proportional :
    ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ G V) (σ : Representation ℂ G W) (N : ℕ)
      (S : Fin (N + 1) → Subrepresentation π), Monotone S → S 0 = ⊥ → S (Fin.last N) = ⊤ →
      ∀ t₀ : Fin N,
        (∀ φ ψ : (subQuot (S t₀.succ) (S t₀.castSucc)).IntertwiningMap σ,
          φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) →
        (∀ t : Fin N, t ≠ t₀ →
          ∀ φ : (subQuot (S t.succ) (S t.castSucc)).IntertwiningMap σ, φ.toLinearMap = 0) →
        ∀ φ ψ : π.IntertwiningMap σ,
          φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap := by
  intro G V W _ _ _ _ _ π σ N S _ hS0 hST t₀ hmult hzero φ ψ
  have happ : ∀ (f : π.IntertwiningMap σ) (v : V), f.toLinearMap v = f v :=
    fun f v => Representation.IntertwiningMap.toLinearMap_apply π σ f v
  have hbot : ∀ f : π.IntertwiningMap σ, ∀ v ∈ (S ⟨0, Nat.succ_pos N⟩).toSubmodule, f v = 0 := by
    intro f v hv
    have e0 : (⟨0, Nat.succ_pos N⟩ : Fin (N + 1)) = 0 := by
      first
        | exact Fin.mk_zero
        | exact Fin.ext (by simp)
    rw [e0, hS0] at hv
    have hv0 : v = 0 := by
      first
        | exact (Submodule.mem_bot ℂ).1 hv
        | exact hv
        | simpa using hv
        | exact (Submodule.mem_bot ℂ).1
            ((bot_le : (⊥ : Subrepresentation π) ≤
              ⟨⊥, fun g w hw => by rw [(Submodule.mem_bot ℂ).1 hw, map_zero]; exact Submodule.zero_mem _⟩) hv)
    rw [hv0, ← happ, map_zero]
  have htop : ∀ v : V, v ∈ (S (Fin.last N)).toSubmodule := by
    intro v
    rw [hST]
    first
      | exact Submodule.mem_top
      | trivial
      | exact (le_top : (⟨⊤, fun _ _ _ => Submodule.mem_top⟩ : Subrepresentation π) ≤ ⊤)
          (Submodule.mem_top (x := v))
      | simp
  have hlow : ∀ f : π.IntertwiningMap σ, ∀ v ∈ (S t₀.castSucc).toSubmodule, f v = 0 := fun f =>
    GlobalTheory.CompanionTheory.Filtration.vanish_climb S f 0 (Nat.succ_pos N) (hbot f)
      t₀.val (Nat.zero_le _) (Nat.lt_succ_of_lt t₀.isLt)
      (fun t _ ht => hzero t (by rintro rfl; exact lt_irrefl _ ht))
  have hup : ∀ f : π.IntertwiningMap σ, (∀ v ∈ (S t₀.succ).toSubmodule, f v = 0) → ∀ v, f v = 0 := by
    intro f hf v
    have h := GlobalTheory.CompanionTheory.Filtration.vanish_climb S f (t₀.val + 1)
      (Nat.succ_lt_succ t₀.isLt) hf N t₀.isLt (Nat.lt_succ_self N)
      (fun t h1 _ => hzero t (by rintro rfl; exact Nat.not_succ_le_self _ h1))
    exact h v (htop v)
  have hdesc : ∀ (f : π.IntertwiningMap σ) (hf : ∀ v ∈ (S t₀.castSucc).toSubmodule, f v = 0) (v : V)
      (hv : v ∈ (S t₀.succ).toSubmodule),
      (GlobalTheory.CompanionTheory.Filtration.descend f (S t₀.succ) (S t₀.castSucc) hf).toLinearMap
        (Submodule.Quotient.mk ⟨v, hv⟩) = f v := by
    intro f hf v hv
    first
      | rfl
      | simp [GlobalTheory.CompanionTheory.Filtration.descend, Submodule.liftQ_apply]
  rcases hmult (GlobalTheory.CompanionTheory.Filtration.descend φ (S t₀.succ) (S t₀.castSucc) (hlow φ))
      (GlobalTheory.CompanionTheory.Filtration.descend ψ (S t₀.succ) (S t₀.castSucc) (hlow ψ)) with h | ⟨c, hc⟩
  · left
    apply LinearMap.ext
    intro v
    rw [LinearMap.zero_apply, happ]
    refine hup φ ?_ v
    intro w hw
    rw [← hdesc φ (hlow φ) w hw, h, LinearMap.zero_apply]
  · right
    refine ⟨c, ?_⟩
    let χ : π.IntertwiningMap σ :=
      { toLinearMap := ψ.toLinearMap - c • φ.toLinearMap
        isIntertwining' := fun g => by
          first
            | rw [LinearMap.sub_comp, LinearMap.smul_comp, LinearMap.comp_sub, LinearMap.comp_smul,
                ψ.isIntertwining' g, φ.isIntertwining' g]
            | (ext v
               have h1 := LinearMap.congr_fun (ψ.isIntertwining' g) v
               have h2 := LinearMap.congr_fun (φ.isIntertwining' g) v
               simp only [LinearMap.comp_apply] at h1 h2
               simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, h1, h2,
                 map_sub, map_smul]) }
    have hχ : ∀ v, χ v = ψ v - c • φ v := by
      intro v
      rw [← happ, ← happ, ← happ]
      rfl
    have hχS : ∀ v ∈ (S t₀.succ).toSubmodule, χ v = 0 := by
      intro v hv
      rw [hχ, ← hdesc ψ (hlow ψ) v hv, ← hdesc φ (hlow φ) v hv, hc, LinearMap.smul_apply, sub_self]
    apply LinearMap.ext
    intro v
    have h := hup χ hχS v
    rw [hχ, sub_eq_zero] at h
    rw [LinearMap.smul_apply, happ, happ]
    exact h

end GlobalTheory.CompanionTheory.Filtration
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalExistenceProperPushforward
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE

theorem core_integral_step : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] (J : X.IdealSheafData) [IsIntegral J.subscheme] {Z : Scheme.{0}} [Z.Over (Spec (.of A))], Statement I (⊥ : Z.IdealSheafData) → ∀ (ψ : Z ⟶ J.subscheme), IsProper ψ → (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ (W : J.subscheme.Opens), (W : Set J.subscheme).Nonempty → IsIso (ψ ∣_ W) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → (∀ e, Killed J (S e)) → PropSupp A (S 0) → ∃ (D : Subobject E) (c : ℕ) (J' : X.IdealSheafData), (D : X.Modules).IsQuasicoherent ∧ PropSupp A D ∧ (∀ e, S (e + c) ≤ D ⊔ powSub I E (e + 1)) ∧ J < J' ∧ ∀ (n : ℕ) (U : X.affineOpens) (a : Γ(X, U)), a ∈ J'.ideal U → ∀ x ∈ secs D U, a • x ∈ secs (S n) U := by
  intro A _ _ I _ X _ _ _ _ J _ Z _ hZ ψ hψ hover W hW hiso E hE S hS hK hP
  have hln : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of A))
  have hcs : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of A))
  have hφ : IsProper (ψ ≫ J.subschemeι) := by
    haveI := hψ
    infer_instance
  have hcl := GlobalTheory.T.closed_system_pullback I (ψ ≫ J.subschemeι) hover hE hS
  have hps := GlobalTheory.T.proper_support_pullback_system I (ψ ≫ J.subschemeι) hφ hover hE hS hP
  have hEZ := isCoherent_pullback (ψ ≫ J.subschemeι) hE
  obtain ⟨B, hBq, hBP, hB⟩ := hZ _ hEZ _ hcl (fun e U a ha x => by
    have ha0 : a = 0 := by simpa using ha
    subst ha0
    exact ⟨0, by rw [map_zero, zero_smul]⟩) hps
  have := hEZ.1
  have hG : IsCoherent (cokernel B.arrow) := isCoherent_cokernel B.arrow hEZ
  have hP' := GlobalTheory.T.proper_pushforward_coherent (ψ ≫ J.subschemeι) hφ hG
  have := hP'.1
  have hE1 := hE.1
  have hDq : ((adjKer (ψ ≫ J.subschemeι) B : Subobject E) : X.Modules).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (kernelSubobjectIso (adjMap (ψ ≫ J.subschemeι) B)).symm
      (isCoherent_kernel (adjMap (ψ ≫ J.subschemeι) B) hE).1
  obtain ⟨c, hc⟩ := GlobalTheory.T.proper_pullback_system_quasicoherent I (ψ ≫ J.subschemeι) hφ hover hE hS B hBq hB
  obtain ⟨J₀, hJ₀, hJ₀J⟩ := GlobalTheory.T.nonempty_open_ideal_not_nilpotent J W hW
  obtain ⟨m, hm⟩ := GlobalTheory.T.ideal_power_kills_system hE (adjKer (ψ ≫ J.subschemeι) B) hDq S hS.qcoh J₀
    (fun V f hf x hx => GlobalTheory.T.proper_birational_closed_system I J ψ hψ hover W hiso hE hS hK B hB V f (hJ₀ V f hf) x hx)
  refine ⟨adjKer (ψ ≫ J.subschemeι) B, c, J ⊔ powIdeal J₀ m, hDq,
    GlobalTheory.T.pushforward_closed_system_auxiliary (ψ ≫ J.subschemeι) hφ hover B hBP, hc, ?_, ?_⟩
  · exact lt_of_le_of_ne le_sup_left (fun h => hJ₀J m (h ▸ le_sup_right))
  · intro n U a ha x hx
    obtain ⟨a₁, h₁, a₂, h₂, rfl⟩ := Submodule.mem_sup.1 ha
    rw [add_smul]
    obtain ⟨y, rfl⟩ := hx
    exact (secsSub (S n) U).add_mem (hK n U a₁ h₁ _) (hm n U a₂ h₂ _ ⟨y, rfl⟩)

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenHom
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.GE.TwGen

variable {X : Scheme.{0}} {H : ReciprocityTheory.ChartRestriction.G.Semi.LB X}

def genHom (hH : H.IsLB) {P : X.Modules} (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)) :
    GlobalTheory.twistZ (SheafOfModules.unit X.ringCatSheaf) H (-n) ⟶ P :=
  GlobalTheory.Twist.map (GlobalTheory.lbZPow H (-n)) (GlobalTheory.QCoh.sectionHom b) ≫
    (GlobalTheory.Twist.twistZAddIso P hH (add_neg_cancel n)).hom ≫ (GlobalTheory.Twist.twistZZeroIso P hH).inv

def genSub (hH : H.IsLB) {P : X.Modules} (n : ℤ) (b : Γ(GlobalTheory.twistZ P H n, ⊤)) : Subobject P :=
  imageSubobject (genHom hH n b)

end GlobalTheory.CompanionTheory.GE.TwGen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedModuleSystemRestriction
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

open MvPolynomial in

theorem exists_finite_sub (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢]
    [DirectSum.Decomposition 𝒢]
    (h : ∀ i : ι, ∃ T : Finset G, ∀ y : G, ∃ k : ℕ,
      (X i : MvPolynomial ι R) ^ k • y ∈ Submodule.span (MvPolynomial ι R) (T : Set G)) :
    ∃ K : Submodule (MvPolynomial ι R) G, K.IsHomogeneous 𝒢 ∧
      Module.Finite (MvPolynomial ι R) K ∧ ∀ (t : ℤ) (I : Finset ι), I.Nonempty →
        Function.Bijective (homLocMap (isGradedMap_subtype 𝒢 K) I t) := by
  obtain ⟨r, d, g, hg, hsat⟩ := exists_homogeneous_family_saturating ι R G 𝒢 h
  have hhom : (Submodule.span (MvPolynomial ι R) (Set.range g)).IsHomogeneous 𝒢 :=
    isHomogeneous_span_gr 𝒢 (by
      rintro _ ⟨l, rfl⟩
      exact ⟨d l, hg l⟩)
  refine ⟨_, hhom, Module.Finite.span_of_finite _ (Set.finite_range g), fun t I ⟨i, hi⟩ => ?_⟩
  letI := grSubDecomposition 𝒢 hhom
  exact homLocMap_bijective_of_X _ hi
    (fun m hm => ⟨0, by
      rw [(map_eq_zero_iff _ (Submodule.injective_subtype _)).1 hm, smul_zero]⟩)
    (fun y => by simpa using hsat i y) t

theorem pairs_of_cube {ι : Type} [LinearOrder ι] {A : Type} [CommRing A] (C : Cube.{0} ι A)
    (hpairs : ∀ c : ∀ i j : ι, C.obj {i, j}, (∀ i j k, Cube.res C (sub_triple_ij i j k) (c i j) +
      Cube.res C (sub_triple_jk i j k) (c j k) = Cube.res C (sub_triple_ik i j k) (c i k)) →
      ∃ b : ∀ i : ι, C.obj {i}, ∀ i j, c i j = Cube.res C (sub_pair_left i j) (b i) -
        Cube.res C (sub_pair_right i j) (b j))
    {P : Finset ι → Type} [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)]
    [∀ S, Module (MvPolynomial ι A) (P S)]
    (Qs : ∀ S, Submodule A (P S))
    (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S')
    (ψ : ∀ I : Finset ι, I.Nonempty → (C.obj I →ₗ[A] Qs I))
    (hb : ∀ I hI, Function.Bijective (ψ I hI))
    (hr : ∀ I J (hI : I.Nonempty) (hJ : J.Nonempty) (h : I ⊆ J) (z : C.obj I),
      (ψ J hJ (Cube.res C h z) : P J) = res I J h (ψ I hI z : P I))
    (c : ∀ i j : ι, P {i, j}) (hc : ∀ i j, c i j ∈ Qs {i, j})
    (hcoc : ∀ i j k, res {i, j} {i, j, k} (sub_triple_ij i j k) (c i j) +
      res {j, k} {i, j, k} (sub_triple_jk i j k) (c j k) =
        res {i, k} {i, j, k} (sub_triple_ik i j k) (c i k)) :
    ∃ b : ∀ i : ι, P {i}, (∀ i, b i ∈ Qs {i}) ∧
      ∀ i j, c i j = res {i} {i, j} (sub_pair_left i j) (b i) -
        res {j} {i, j} (sub_pair_right i j) (b j) := by
  have n2 (i j : ι) : ({i, j} : Finset ι).Nonempty := Finset.insert_nonempty _ _
  have n1 (i : ι) : ({i} : Finset ι).Nonempty := Finset.singleton_nonempty i
  have n3 (i j k : ι) : ({i, j, k} : Finset ι).Nonempty := Finset.insert_nonempty _ _
  choose c' hc' using fun i j => (hb {i, j} (n2 i j)).2 ⟨c i j, hc i j⟩
  have hv (i j : ι) : (ψ _ (n2 i j) (c' i j) : P {i, j}) = c i j := congrArg Subtype.val (hc' i j)
  obtain ⟨b', hb'⟩ := hpairs c' fun i j k => by
    refine (hb _ (n3 i j k)).1 (Subtype.ext ?_)
    rw [map_add, Submodule.coe_add, hr _ _ (n2 i j) (n3 i j k), hr _ _ (n2 j k) (n3 i j k),
      hr _ _ (n2 i k) (n3 i j k), hv, hv, hv, hcoc]
  refine ⟨fun i => ψ _ (n1 i) (b' i), fun i => (ψ _ (n1 i) (b' i)).2, fun i j => ?_⟩
  rw [← hv i j, hb' i j, map_sub, Submodule.coe_sub, hr _ _ (n1 i) (n2 i j),
    hr _ _ (n1 j) (n2 i j)]

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem serre_cech_pairs : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (A : Type) [CommRing A] [IsNoetherianRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] [∀ S, IsScalarTower A (MvPolynomial ι A) (P S)] (𝒢 : ∀ S, ℤ → Submodule A (P S)) [∀ S, PolyGradedSMul ι (𝒢 S)] [∀ S, DirectSum.Decomposition (𝒢 S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S S' (h : S ⊆ S'), IsGradedMap (𝒢 S) (𝒢 S') (res S S' h)) → (∀ S (h : S ⊆ S) a, res S S h a = a) → (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (i : ι) (S : Finset ι), i ∈ S → Function.Bijective fun m : P S => (MvPolynomial.X i : MvPolynomial ι A) • m) → (∀ (S : Finset ι) (j : ι) (a : P S), S.Nonempty → res S (insert j S) (Finset.subset_insert j S) a = 0 → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • a = 0) → (∀ (S : Finset ι) (j : ι) (b : P (insert j S)), S.Nonempty → ∃ k : ℕ, (MvPolynomial.X j : MvPolynomial ι A) ^ k • b ∈ LinearMap.range (res S (insert j S) (Finset.subset_insert j S))) → (∀ i : ι, ∃ s : Finset (P {i}), ∀ m : P {i}, ∃ k : ℕ, (MvPolynomial.X i : MvPolynomial ι A) ^ k • m ∈ Submodule.span (MvPolynomial ι A) (s : Set (P {i}))) → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → ∀ c : ∀ i j : ι, P {i, j}, (∀ i j, c i j ∈ 𝒢 {i, j} t) → (∀ i j k, res {i, j} {i, j, k} (sub_triple_ij i j k) (c i j) + res {j, k} {i, j, k} (sub_triple_jk i j k) (c j k) = res {i, k} {i, j, k} (sub_triple_ik i j k) (c i k)) → ∃ b : ∀ i : ι, P {i}, (∀ i, b i ∈ 𝒢 {i} t) ∧ ∀ i j, c i j = res {i} {i, j} (sub_pair_left i j) (b i) - res {j} {i, j} (sub_pair_right i j) (b j) := by
  intro ι _ _ A _ _ P _ _ _ _ 𝒢 _ _ res hgr hid hcomp hbij hinj hsurj hfin
  have iI := GlobalTheory.CompanionTheory.FormalAlg.IterInj.iter_localisation_injective ι A P res hid hcomp hinj
  have iS := GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.xProd_pow_smul_mem_range_res_iter ι A P res hid hcomp hsurj
  have g1 := GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.exists_compatible_family_of_singleton ι A P res hid hcomp hinj hsurj
  have K1 := GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.smul_eq_zero_of_ev_eq_zero ι A P res hcomp iI
  have K2 := GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.exists_xProd_pow_smul_eq_ev ι A P res hcomp iS g1
  letI : DirectSum.Decomposition (glueGr res 𝒢) := glueDec 𝒢 hgr
  have sat : ∀ i : ι, ∃ T : Finset (glue res), ∀ y : glue res, ∃ k : ℕ,
      (MvPolynomial.X i : MvPolynomial ι A) ^ k • y ∈
        Submodule.span (MvPolynomial ι A) (T : Set (glue res)) := by
    intro i
    refine GlobalTheory.CompanionTheory.FormalAlg.Lift.SerreSat.saturated_fg_of_powerTorsion_ker_coker (MvPolynomial ι A) (MvPolynomial.X i) (glue res) (P {i})
      (ev res {i} (Finset.singleton_nonempty i)) (fun m hm => ?_) (fun f => ?_) (hfin i)
    · simpa [xProd] using K1 {i} _ m hm
    · simpa [xProd] using K2 {i} (Finset.singleton_nonempty i) f
  obtain ⟨K, hK, hKf, hb⟩ := exists_finite_sub ι A (glue res) (glueGr res 𝒢) sat
  letI := grSubDecomposition (glueGr res 𝒢) hK
  obtain ⟨t₀, ht₀⟩ := cubeComplex_grCube_exactAt_of_finite ι A K (grSub (glueGr res 𝒢) K) hKf
  refine ⟨t₀, fun t ht c hc hcoc => ?_⟩
  have hex := (cechComplex_exactAt_succ_iff _ 0).1
    ((cechComplex_exactAt_succ_iff_cube _ 0).2 (ht₀ t ht 2))
  obtain ⟨φ, hφb, hφr⟩ := GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.exists_homLoc_pieces_compatible ι A (glue res) (glueGr res 𝒢) P 𝒢 res (ev res)
    (isGradedMap_ev 𝒢 hgr) (fun I J hI hJ h m => res_ev hcomp hI hJ h m) hbij K1 K2 t
  refine pairs_of_cube (grCube ι (grSub (glueGr res 𝒢) K) t) (GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue.exists_coboundary_of_pairs_cocycle ι A _ hex)
    (fun S => 𝒢 S t) res
    (fun I hI => φ I hI ∘ₗ homLocMap (isGradedMap_subtype _ K) I t)
    (fun I hI => (hφb I hI).comp (hb t I hI)) (fun I J hI hJ h z => ?_) c hc hcoc
  have e : homLocMap (isGradedMap_subtype (glueGr res 𝒢) K) J t (Cube.res _ h z) =
      homLocRes _ h t (homLocMap (isGradedMap_subtype (glueGr res 𝒢) K) I t z) :=
    homLocMap_homLocRes _ h t z
  exact (congrArg (fun w => ((φ J hJ w : 𝒢 J t) : P J)) e).trans (hφr I J hI hJ h _)

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GrothendieckExistenceClosedProj
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.GE

theorem geClosedProj : GEClosedProj := by
  intro R _ _ I hI N P Cs i β hi hβ
  obtain ⟨hbase, hsat, hanti, hcompat⟩ := GlobalTheory.T.thickening_vanishing_ideal_system R I N Cs i β hi hβ
  obtain ⟨n₀, hlift⟩ := GlobalTheory.T.homogeneous_ideal_filtration_saturated R I N (fun e => vanIdeal (i e ≫ thickι R I N e))
    (fun e => vanIdeal_homog _) hbase hsat hcompat
  obtain ⟨J, hJ, h⟩ := GlobalTheory.T.homogeneous_lift_adic_filtration R I hI N (fun e => vanIdeal (i e ≫ thickι R I N e))
    (fun e => vanIdeal_homog _) hbase hanti n₀ hlift
  exact GlobalTheory.T.homogeneous_ideal_le_thickening R I N Cs i β hi hβ J hJ (fun e => (h e).1) (fun e => (h e).2)

end GlobalTheory.CompanionTheory.GE
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitarisableDegenerateSeries
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.DegenerateSeries

theorem isUnitarisable_degenerateSeries (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (_ : IsSmoothChar χ₁)
    (_ : IsSmoothChar χ₂) (h₁ : IsUnitaryChar χ₁) (h₂ : IsUnitaryChar χ₂) :
    IsUnitarisable (parInd (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)) := by
  apply GlobalTheory.SmGL.UnitInd.isUnitarisable_prod₂
  · rw [GlobalTheory.SmGL.detRep, GlobalTheory.SmGL.isUnitarisable_ofChar_iff]
    intro g
    exact h₁ _
  · rw [GlobalTheory.SmGL.detRep, GlobalTheory.SmGL.isUnitarisable_ofChar_iff]
    intro g
    exact h₂ _

end GlobalTheory.CompanionTheory.DegenerateSeries
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerOpsComm
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.UV

variable {X : Scheme.{0}} {k : ℕ} (M : ℕ → X.Modules) (T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1))

def kerSeq (e : ℕ) : X.Modules := kernel (T (Fin.last k) e)

def cokSeq (e : ℕ) : X.Modules := cokernel (T (Fin.last k) e)

variable {M T}

def kerOps (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (i : Fin k) (e : ℕ) :
    kerSeq M T e ⟶ kerSeq M T (e + 1) :=
  kernel.map (T (Fin.last k) e) (T (Fin.last k) (e + 1)) (T i.castSucc e) (T i.castSucc (e + 1))
    (hc _ _ e)

def cokOps (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (i : Fin k) (e : ℕ) :
    cokSeq M T e ⟶ cokSeq M T (e + 1) :=
  cokernel.map (T (Fin.last k) e) (T (Fin.last k) (e + 1)) (T i.castSucc e) (T i.castSucc (e + 1))
    (hc _ _ e)

theorem kerOps_comm (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (i j : Fin k) (e : ℕ) :
    kerOps hc i e ≫ kerOps hc j (e + 1) = kerOps hc j e ≫ kerOps hc i (e + 1) := by
  dsimp only [kerOps, kerSeq]
  apply equalizer.hom_ext
  simp only [kernel.map, Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc]
  rw [hc i.castSucc j.castSucc e]

theorem cokOps_comm (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (i j : Fin k) (e : ℕ) :
    cokOps hc i e ≫ cokOps hc j (e + 1) = cokOps hc j e ≫ cokOps hc i (e + 1) := by
  dsimp only [cokOps, cokSeq]
  apply coequalizer.hom_ext
  simp only [cokernel.map, Category.assoc, cokernel.π_desc, cokernel.π_desc_assoc]
  simp only [← Category.assoc, hc i.castSucc j.castSucc (e + 1)]

end GlobalTheory.CompanionTheory.GE.UV
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSubReductionMemStatement
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_sub_reduction_mem : ∀ (l : ℕ) [Fact l.Prime] (M k : ℕ), ∀ x ∈ Lat.sub (Lat.fk l (k + 1)) (xi0 l) l M, Lat.dk l k x ∈ Lat.sub (Lat.fk l k) (xi0 l) l M := by
  first | exact @GlobalTheory.CompanionTheory.LatLevel.dk_mem_sub | exact GlobalTheory.CompanionTheory.LatLevel.dk_mem_sub | (intros; apply GlobalTheory.CompanionTheory.LatLevel.dk_mem_sub <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFiltrationSpanTPowStatement
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_filtration_span_t_pow : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (r : ℕ) (t : (per l K).P), (t : (per l K).B) = (per l K).tB → pdP (lev h k).γB r = Ideal.span {(lev h k).toB t ^ r} := by
  first | exact @GlobalTheory.CompanionTheory.LatPdpB.dividedPowerFiltration_lev_eq_span_pow | exact GlobalTheory.CompanionTheory.LatPdpB.dividedPowerFiltration_lev_eq_span_pow | (intros; apply GlobalTheory.CompanionTheory.LatPdpB.dividedPowerFiltration_lev_eq_span_pow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisFixesFieldStatement
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_galois_fixes_field : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g (a : K), (lev h k).σB g (algebraMap K (lev h k).B a) = algebraMap K (lev h k).B a := by
  first | exact @GlobalTheory.CompanionTheory.LatC.sigmaB_fixes_K | exact GlobalTheory.CompanionTheory.LatC.sigmaB_fixes_K | (intros; apply GlobalTheory.CompanionTheory.LatC.sigmaB_fixes_K <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisFixesIntegersStatement
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_galois_fixes_integers : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g (a : OK l K), (lev h k).σA g (algebraMap (OK l K) (lev h k).A a) = algebraMap (OK l K) (lev h k).A a := by
  first | exact @GlobalTheory.CompanionTheory.LatC.sigA_fix | exact GlobalTheory.CompanionTheory.LatC.sigA_fix | (intros; apply GlobalTheory.CompanionTheory.LatC.sigA_fix <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelGaloisIsDPMorphismStatement
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_galois_isDPMorphism : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ g, IsDPMorphism (lev h k).γ (lev h k).γ ((lev h k).σA g) := by
  first | exact @GlobalTheory.CompanionTheory.LatSigDP.sigA_isDPMorphism | exact GlobalTheory.CompanionTheory.LatSigDP.sigA_isDPMorphism | (intros; apply GlobalTheory.CompanionTheory.LatSigDP.sigA_isDPMorphism <;> assumption)
end

