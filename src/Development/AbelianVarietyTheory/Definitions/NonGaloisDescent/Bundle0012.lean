import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TameGeneratorProjectors
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0088
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0085
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import GroundTheory.LocalFields.Bundle0010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
section
noncomputable section

namespace GlobalTheory.TripleGal

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.Pst
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf)

def rk1 {Γ K : Type} [Group Γ] [CommRing K] (χ : Γ →* Kˣ) : Γ →* GL (Fin 1) K :=
  (Units.map (Matrix.scalar (Fin 1) : K →+* Matrix (Fin 1) (Fin 1) K).toMonoidHom).comp χ

def Temp (D : D7) : Prop :=
  ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π → ∀ w, D.naut.tempered (D.naut.locG π w)

open Classical in

def GalAbove (D : D7) : Prop :=
  ∀ (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar l)), IsGaloisRepOf D π l ι r →
    ∀ w ∈ placesOver D.host.E l, ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), GlobalTheory.Pst.Induces Bw →
      IsdRAt (D.loc l) Bw (r.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) ∧
      (D.naut.unr (D.naut.locG π w) → IsCrysAt (D.loc l) Bw (r.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)) ∧
      (D.naut.mono0 (D.naut.locG π w) → IsPotCrysAt (D.loc l) Bw (r.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)) ∧
      ∀ (τ : D.host.E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        ∃ J : Multiset ℤ, IsJumpsAt (D.loc l) Bw (r.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ J ∧
          J.map (fun n : ℤ => (n : ℂ)) =
            (D.naut.infG π (ι.toRingHom.comp τ)).map fun z => ((D.R.r : ℂ) - 1) / 2 - z

def CharAbove : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (ι : Qbar l ≃+* ℂ)
    (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ) (μ : G E Ω →* (Qbar l)ˣ),
    IsAlgPos χ n → Continuous μ → IsLAdicOf art ι χ n μ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
      IsdRAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) ∧ IsPotCrysAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) ∧
      (χ.UnrAt w → IsCrysAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype)) ∧
      ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
        IsJumpsAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) τ {-n (ι.toRingHom.comp τ)}

def MonoG (D : D7) : Prop :=
  ∀ (σ : D.what₂.FT) (π : D.naut.CG D.R.r), D.nd.goodRow σ → D.naut.csd π → D.naut.ralg π →
    (∀ k v, D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG π (D.naut.plGw k v))) →
    ∀ k, ∀ w ∈ placesOver D.host.E (D.host.g k), D.naut.mono0 (D.naut.locG π w)

structure Mid (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i) : Prop where
  unr : UnrRho i s
  hodge : HodgeL bkP i s
  pure : ∃ ι, Pure i s ι
  jumps : ∃ ι J, JumpsAre bkP i s ι J ∧ GoodJ D J
  dual : FrobDual i s
  hk : HkFrob i s

def LocTrue (D : D7) (i : D.ntw.Tw) : Prop :=
  ∃ AI, Nonempty (LocTied (D.ntw.l i) (D.loc (D.ntw.l i)) AI)

end GlobalTheory.TripleGal

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IotaInjOfTensorInj
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.RingsModel

variable {l : ℕ} [Fact l.Prime]

theorem exists_core_facts (l : ℕ) [Fact l.Prime] : ∃ C : Core l, C.PhiInj ∧ C.IotaInj ∧ C.InvdR := by
  obtain ⟨C⟩ := nonempty_core l
  exact ⟨C, phiB_injective l, (ULaws.u_laws l C).2.2.2.1, fun K b hb => InvDR.invariants_BdR l C K b hb⟩

theorem iotaInj_of_tensorInj (C : Core l) (h : C.TensorInj) : C.IotaInj := by
  refine (injective_iff_map_eq_zero C.ι).2 fun b hb => ?_
  refine h 1 (fun _ => 1) ?_ (fun _ => b) (by simp [hb]) 0
  exact linearIndependent_unique_iff.2 one_ne_zero

theorem sigma_tB (C : Core l) (g : GQ l) :
    Per.σB g C.tB = C.qB (((C.χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) * C.tB := by
  have h1 : Per.σB g C.tB = algebraMap (Per.Acris l) (Per.Bcris l) (sigA g C.t) := by
    have := plusToB_sig g (algebraMap (Per.Acris l) (BcrisP l) C.t)
    rw [sigP_alg, plusToB_alg, plusToB_alg] at this
    exact this.symm
  rw [h1, TAct.t_act l C g, map_mul]
  congr 1
  apply (ULaws.u_laws l C).2.2.2.1
  rw [C.ι_j, InvDR.j_alg, ← C.o_sec.z]
  exact (C.ι_u (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (((C.χ g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]))).symm

theorem phi_tB (C : Core l) : Per.φB l C.tB = ((l : ℕ) : Per.Bcris l) * C.tB := by
  have := plusToB_phi (algebraMap (Per.Acris l) (BcrisP l) C.t)
  rw [phiP_alg, plusToB_alg, plusToB_alg, TPhi.t_phi l C, map_mul, map_natCast] at this
  exact this.symm

theorem inv_t_not_plus (C : Core l) (x : BcrisP l) : plusToB l x * C.tB ≠ 1 := by
  intro h
  have h2 := congrArg C.ι h
  rw [map_mul, map_one, C.ι_plusToB, Core.tB, C.ι_j, ← map_mul,
    ← map_one (algebraMap (Per.BdRp l) (Per.BdR l))] at h2
  have h3 := congrArg (Per.θD l) ((BdRField.bdR_isField l).2.1 h2)
  have h4 : Per.θD l (C.j C.t) = 0 := by
    have := (core_t_unit_fil l C).2.1
    rw [← (thetaD_onto_ker l).2] at this
    exact this
  rw [map_mul, h4, mul_zero, map_one] at h3
  exact zero_ne_one h3

variable {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}

theorem qB_of_fits (h : Fits T C) (x : ℚ_[l]) : T.eB (algebraMap ℚ_[l] P.R.B x) = C.qB x := by
  rw [IsScalarTower.algebraMap_apply ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B, h.u]
  rfl

theorem fund_of_fits (h : Fits T C) : C.Fund := by
  intro b hφ hF
  obtain ⟨b, rfl⟩ := T.eB.surjective b
  obtain ⟨K⟩ : Nonempty (FinExt l) := ⟨⟨⊥, inferInstance⟩⟩
  obtain ⟨c, hc⟩ := (P.PD K).fund b
    (by rw [P.PD_φ]; apply T.eB.injective; rw [T.frob, hφ])
    (by rw [T.fil, P.PD_ι, h.ι]; exact hF)
  exact ⟨c, by rw [← qB_of_fits h, hc]⟩

theorem invB_of_fits (h : Fits T C) : C.InvB := by
  intro K b hb
  obtain ⟨b, rfl⟩ := T.eB.surjective b
  obtain ⟨c, hc⟩ := (P.PD K).invB b fun g => by
    rw [P.PD_actB]; apply T.eB.injective; rw [T.actB]; exact hb g g.2
  refine ⟨⟨c, c.2.2⟩, c.2.1, ?_⟩
  rw [← h.u, ← hc]
  rfl

theorem isField_of_isStd (h : GlobalTheory.Per.IsStd P AI) : IsField P.R.BdR := by
  obtain ⟨T⟩ := h
  exact T.eD.toMulEquiv.isField (BdRField.bdR_isField l).2.2.1

end GlobalTheory.MemLoc.RingsModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField

namespace GlobalTheory.PMon.Ram

open Classical in

def jumpSum {G : Type} [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G) : ℕ :=
  ∑ᶠ t : ℕ, if A ⊓ R t ≤ B then 0 else Nat.card ↥(A ⊓ R t)

section

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

def wild (t : ℕ) : Subgroup (L ≃ₐ[K] L) := lowerRamificationGroup K L ((t : ℤ) + 1)

def AxIn (p : ℕ) : Prop :=
  ∀ (J : Subgroup (L ≃ₐ[K] L)) (x : L), (∀ σ ∈ J, σ x - x ∈ 𝒪[L]) →
    ∃ y : L, (∀ σ ∈ J, σ y = y) ∧ (p : L) ^ 2 * (x - y) ∈ 𝒪[L]

variable {K L} in

def Detects (p r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)) : Prop :=
  ∀ σ₀ ∈ A, σ₀ ∉ B → ∃ (x : L) (a : (L ≃ₐ[K] L) → ℤ),
    (∀ σ ∈ A, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) ∧ ¬ (p : ℤ) ^ r ∣ a σ₀

end

def OrdIs (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] (p E : ℕ) : Prop :=
  IsDiscreteValuationRing.addVal 𝒪[L] (p : 𝒪[L]) = (E : ℕ∞)

def NoTower : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (N : ℕ → Subgroup ↥(GK K)), Antitone N →
    (∀ k, IsOpen (N k : Set ↥(GK K))) →
    (∀ k, ∀ σ ∈ N k, σ ^ l ∈ N (k + 1)) →
    (∀ j, ∀ σ ∈ N 0, σ ^ l ∈ N (j + 1) → σ ∈ N j) →
    (∀ r : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ (ι : Type) (_ : Finite ι) (x : ι → ℂ_[l]) (a : ι → ↥(GK K) → ℤ_[l]),
      (∀ i, ∀ σ ∈ N k, ‖Formalism.Per.σC (σ : GQ l) (x i) - x i - algebraMap ℚ_[l] ℂ_[l] (a i σ : ℚ_[l])‖ ≤ ((l : ℝ)⁻¹) ^ r) ∧
      ∀ σ ∈ N k, (∀ i, (l : ℤ_[l]) ^ r ∣ a i σ) → σ ∈ N (k + r)) →
    ∃ k, ∀ j, IK K ⊓ N k ≤ N j

def NoTowerQ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (N : ℕ → Subgroup (GQ l)), Antitone N →
    (∀ k, IsOpen (N k : Set (GQ l))) →
    (∀ k, ∀ σ ∈ N k, σ ^ l ∈ N (k + 1)) →
    (∀ j, ∀ σ ∈ N 0, σ ^ l ∈ N (j + 1) → σ ∈ N j) →
    (∀ r : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ (ι : Type) (_ : Finite ι) (x : ι → Om l) (a : ι → GQ l → ℤ),
      (∀ i, ∀ σ ∈ N k, ‖σ (x i) - x i - (a i σ : Om l)‖ ≤ ((l : ℝ)⁻¹) ^ r) ∧
      ∀ σ ∈ N k, (∀ i, (l : ℤ) ^ r ∣ a i σ) → σ ∈ N (k + r)) →
    ∃ k, ∀ j, ∀ σ ∈ N k, (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) → σ ∈ N j

end GlobalTheory.PMon.Ram

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RealisesUnitPow
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.Prism
open scoped Formalism.Per

namespace GlobalTheory.BKReal

variable {l : ℕ} [hl : Fact l.Prime]

theorem semiBC_of_basis {A B M N J : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (b : Module.Basis J A M)
    (c : Module.Basis J B N) (h : ∀ i, u (b i) = c i) : SemiBC u := by
  intro Q _ _ v
  refine ⟨c.constr B fun i => v (b i), fun x => ?_, fun w hw => c.ext fun i => ?_⟩
  · exact LinearMap.congr_fun (b.ext (f₁ := (c.constr B fun i => v (b i)).comp u) (f₂ := v) fun i => by
      rw [LinearMap.comp_apply, h, Module.Basis.constr_basis]) x
  · rw [Module.Basis.constr_basis, ← h, hw]

def piMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (J : Type) : (J → A) →ₛₗ[f] (J → B) where
  toFun x i := f (x i)
  map_add' x y := funext fun i => map_add f (x i) (y i)
  map_smul' c x := funext fun i => map_mul f c (x i)

theorem piMap_single {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {J : Type} [DecidableEq J] (i : J) :
    piMap f J (Pi.single i 1) = Pi.single i 1 := by
  ext1 k
  change f (Pi.single (M := fun _ => A) i 1 k) = _
  simp [Pi.single_apply, apply_ite f]

theorem semiBC_piMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (J : Type) [Fintype J]
    [DecidableEq J] : SemiBC (piMap f J) :=
  semiBC_of_basis (Pi.basisFun A J) (Pi.basisFun B J) fun i => by
    rw [Pi.basisFun_apply, Pi.basisFun_apply, piMap_single]

def piFrob {A : Type} [CommRing A] (φ : A →+* A) (d : A) (J : Type) :
    (J → A) →ₛₗ[(algebraMap A (Localization.Away d)).comp φ] LocalizedModule (Submonoid.powers d) (J → A) where
  toFun x := LocalizedModule.mk (piMap φ J x) 1
  map_add' x y := by simp [LocalizedModule.mk_add_mk]
  map_smul' c x := by
    rw [RingHom.comp_apply, algebraMap_smul, LocalizedModule.smul'_mk, LinearMap.map_smulₛₗ]

theorem exists_of_isFrac {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {d : A} {y m : M} {k : ℕ}
    (h : IsFrac d (LocalizedModule.mk y 1) m k) : ∃ r : ℕ, d ^ r • d ^ k • y = d ^ r • m := by
  obtain ⟨⟨_, r, rfl⟩, hr⟩ := LocalizedModule.mk_eq.1 h
  exact ⟨r, by simpa [Submonoid.smul_def] using hr⟩

def unitPow (l : ℕ) (R : Type) [CommRing R] (J : Type) [Fintype J] [DecidableEq J] : FCrys l R where
  M P := J → P.A
  fin _ := inferInstance
  proj _ := inferInstance
  tr f := piMap f.f J
  tr_bc f := semiBC_piMap f.f J
  tr_id _ _ := rfl
  tr_comp _ _ _ := rfl
  Φ P d := piFrob P.D.φ d J
  Φ_bc P d := semiBC_of_basis (Pi.basisFun _ J) ((Pi.basisFun P.A J).ofIsLocalizedModule
    (Localization.Away (d : P.A)) (Submonoid.powers (d : P.A)) (LocalizedModule.mkLinearMap _ _)) fun i => by
      rw [Module.Basis.ofIsLocalizedModule_apply, Pi.basisFun_apply]
      exact congrArg (LocalizedModule.mk · 1) (piMap_single _ i)
  Φ_nat := by
    intro P P' f d d' x m k n j h1 h2
    obtain ⟨r, hr⟩ := exists_of_isFrac h1
    obtain ⟨s, hs⟩ := exists_of_isFrac h2
    refine ⟨r + s, funext fun i => ?_⟩
    have ha : (d : P.A) ^ r * ((d : P.A) ^ k * P.D.φ (x i)) = (d : P.A) ^ r * m i := congrFun hr i
    have hb : (d' : P'.A) ^ s * ((d' : P'.A) ^ j * P'.D.φ (f.f (x i))) = (d' : P'.A) ^ s * n i := congrFun hs i
    have ha' := congrArg f.f ha
    simp only [map_mul, map_pow, f.f_φ] at ha'
    change (f.f d * d') ^ (r + s) * ((d' : P'.A) ^ j * f.f (m i) - f.f d ^ k * n i) = 0
    linear_combination (-(f.f d) ^ s * (d' : P'.A) ^ (r + s + j)) * ha' +
      (f.f d ^ (r + s + k) * (d' : P'.A) ^ r) * hb

def unitPowMap (F : FinExt l) {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J] [DecidableEq J]
    (β : Module.Basis J ℤ_[l] T) : (unitPow l ↥(OL F) J).M (ainfObj F) →ₛₗ[(inclW l).comp (ainfId F).toRingHom]
      (WCb l ⊗[ℤ_[l]] T) :=
  (β.baseChange (WCb l)).equivFun.symm.toLinearMap.comp (piMap ((inclW l).comp (ainfId F).toRingHom) J)

theorem unitPowMap_apply (F : FinExt l) {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J]
    [DecidableEq J] (β : Module.Basis J ℤ_[l] T) (x : J → Ainf l) :
    unitPowMap F β x = ∑ i, inclW l (x i) ⊗ₜ[ℤ_[l]] β i := by
  refine ((β.baseChange (WCb l)).equivFun_symm_apply fun i => inclW l (x i)).trans
    (Finset.sum_congr rfl fun i _ => ?_)
  rw [Module.Basis.baseChange_apply, smul_tmul', smul_eq_mul, mul_one]

theorem sum_frob {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J] (β : J → T) {d : Ainf l}
    (hd : d ≠ 0) (x m : J → Ainf l) (k r : ℕ)
    (h : ∀ i, d ^ r * (d ^ k * WittVector.frobenius (x i)) = d ^ r * m i) :
    inclW l d ^ k • TensorProduct.map (frobW l).toLinearMap LinearMap.id (∑ i, inclW l (x i) ⊗ₜ[ℤ_[l]] β i) =
      ∑ i, inclW l (m i) ⊗ₜ[ℤ_[l]] β i := by
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, frobW_inclW,
    ← mul_left_cancel₀ (pow_ne_zero r hd) (h i), map_mul, map_pow, smul_tmul', smul_eq_mul]

theorem sum_gal {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J] (β : J → T) (g : GQ l)
    (ρ : T →ₗ[ℤ_[l]] T) (hρ : ∀ x, ρ x = x) (x : J → Ainf l) :
    ∑ i, inclW l (Per.σA g (x i)) ⊗ₜ[ℤ_[l]] β i =
      TensorProduct.map (galW l g).toLinearMap ρ (∑ i, inclW l (x i) ⊗ₜ[ℤ_[l]] β i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply, galW_inclW, hρ]

theorem unitPowMap_frob (F : FinExt l) {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J]
    [DecidableEq J] (β : Module.Basis J ℤ_[l] T) (d : Ainf l) (hd : d ≠ 0) (x m : J → Ainf l) (k : ℕ)
    (h : IsFrac d (LocalizedModule.mk (piMap WittVector.frobenius J x) 1) m k) :
    inclW l d ^ k • TensorProduct.map (frobW l).toLinearMap LinearMap.id (unitPowMap F β x) =
      unitPowMap F β m := by
  obtain ⟨r, hr⟩ := exists_of_isFrac h
  rw [unitPowMap_apply, unitPowMap_apply]
  exact sum_frob β hd x m k r fun i => congrFun hr i

theorem unitPowMap_gal (F : FinExt l) {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J]
    [DecidableEq J] (β : Module.Basis J ℤ_[l] T) (g : GQ l) (ρ : T →ₗ[ℤ_[l]] T) (hρ : ∀ x, ρ x = x)
    (x : J → Ainf l) : unitPowMap F β (fun i => Per.σA g (x i)) =
      TensorProduct.map (galW l g).toLinearMap ρ (unitPowMap F β x) := by
  rw [unitPowMap_apply, unitPowMap_apply]
  exact sum_gal β g ρ hρ x

theorem realises_unitPow (F : FinExt l) {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J]
    [DecidableEq J] (β : Module.Basis J ℤ_[l] T) (ρ : ↥(GK F) → (T →ₗ[ℤ_[l]] T)) (hρ : ∀ g x, ρ g x = x) :
    Realises F (unitPow l ↥(OL F) J) (ainfObj F) (ainfId F) T ρ (unitPowMap F β) where
  ainf := isAinf_ainfObj F
  bc := SemiBC.comp_equiv (semiBC_piMap ((inclW l).comp (ainfId F).toRingHom) J) _
  j_φ d hd x m k h := unitPowMap_frob F β d.1 hd x m k h
  j_act g x := unitPowMap_gal F β g (ρ g) (hρ g) x

end GlobalTheory.BKReal
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Small2
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.ResSel

namespace GlobalTheory.StepTwo

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) (s : X.Sig i)

def idl : Ideal (X.O0 i) := Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i)

def Small2 (M : ℕ) (L : Subgroup (GE N)) (z : GE N) : Prop :=
  Small i s L z ∧ (∀ g ∈ L, ∀ ζ : N.Om, ζ ^ (2 * X.l i ^ M) = 1 → g ζ = ζ) ∧ ∀ g ∈ L, ∀ a b, (Tmat i s g - 1) a b ∈ idl i

variable (M : ℕ) {R n : ℕ} (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M))))

def PiLocalization₂ (A : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host) : Prop :=
  SlopeTestRemainingChoices X i M A P (fun q => d (P q)) ∧
    (∀ a, (∀ v, Over (P (.inl a)) v → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → Ine (F := D.host.E) B ≤ L) ∧
      ∀ σ : GE N, IsFrob (N.plOm.1 (P (.inl a))) (normV (P (.inl a))) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ L) ∧
    ∀ a, DecV N (P (.inr a)) ≤ L ∧ ∀ (b : Fin R) (σ : GE N), IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) σ →
      d (P (.inl b)) σ = Multiplicative.ofAdd (if a.val = b.val then 1 else 0)

def NF (P : Fin R ⊕ Fin n → PlE D.host) (c : ℕ) : Prop :=
  ∀ Q, IsQ P Q → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin n))),
    Computes bkP i s M (fun q => d (P q)) Q Φ → ∀ F, toLam X i M (Fin R ⊕ Fin n) F = Φ.det →
      ∃ m : Fin R ⊕ Fin n →₀ ℕ, m.degree < c ∧ F.coeff m ∉ idl i

def NFit (P : Fin R ⊕ Fin n → PlE D.host) (c : ℕ) : Prop :=
  ∀ Q, IsQ P Q → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M (Fin R ⊕ Fin n))),
    Computes bkP i s M (fun q => d (P q)) Q Φ → a = 0 ∨ ∃ b b', ∀ F, toLam X i M (Fin R ⊕ Fin n) F = Φ.adjugate b b' →
      ∃ m : Fin R ⊕ Fin n →₀ ℕ, m.degree < c ∧ (∀ j : Fin R, n ≤ j.val → m (.inl j) = 0) ∧ IsUnit (F.coeff m)

def Ext (P : Fin R ⊕ Fin n → PlE D.host) (P' : Fin R ⊕ Fin (n + 1) → PlE D.host) : Prop :=
  ∀ q, P' (Sum.map id Fin.castSucc q) = P q

def Start : Prop :=
  ∀ (M R n : ℕ) d A L z (P : Fin R ⊕ Fin n → PlE D.host) (φ φ' : Fin n → GE N), n ≤ R → 4 * D.R.r * n + 2 < X.l i ^ M →
    IsTameInertiaElementAtTwistPrime X i z → Small i s L z → PiLocalization₂ i M d A L z P →
    (∀ a, IsFrob (N.plOm.1 (P (.inr a))) (normV (P (.inr a))) (φ a) ∧ IsCj X (φ a) (φ' a)) → Corank bkP i s φ φ' 1 →
    NFit bkP i s M d P (4 * D.R.r * n + 1)

def Grow : Prop :=
  0 < nu X i → ∀ (M R n : ℕ) d A L z (P : Fin R ⊕ Fin n → PlE D.host) (P' : Fin R ⊕ Fin (n + 1) → PlE D.host) (c : ℕ), n < R →
    c + 2 * D.R.r ≤ X.l i ^ (M - nu X i - 1) → nu X i + 2 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A L z P' → Ext P P' →
    (NF bkP i s M d P c → NF bkP i s M d P' (c + 2 * D.R.r)) ∧ (NFit bkP i s M d P c → NFit bkP i s M d P' (c + 2 * D.R.r))

def Step : Prop :=
  0 < nu X i → ∀ (M R n : ℕ) H S d A L z (P : Fin R ⊕ Fin n → PlE D.host) (w e : ℕ), n < R →
    IsDiscreteValuationRing.addVal (X.O0 i) ((X.l i : X.O0 i) ^ nu X i) = e →
    2 * (e + 1) * w + 2 + 2 * D.R.r ≤ X.l i ^ (M - nu X i - 1) → nu X i + 2 ≤ M →
    AdmFam X i M H S d → L ≤ H → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A L z P → NFit bkP i s M d P (w + 1) →
    ∃ P' : Fin R ⊕ Fin (n + 1) → PlE D.host, Ext P P' ∧ PiLocalization₂ i M d A L z P' ∧
      NF bkP i s M d P' (2 * (e + 1) * w + 2 + 2 * D.R.r)

end GlobalTheory.StepTwo
end
end

