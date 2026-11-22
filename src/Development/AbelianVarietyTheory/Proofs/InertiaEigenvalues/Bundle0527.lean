import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0518
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0252
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0493
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0047
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0495
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CutCocFinsetCommon
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX.Combine

variable {O V ι Γ Q G C : Type} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup Q] [Module O Q]

def blk (act : ι → Γ → V → V) {a : ℕ} (x : Fin a → ι) (γ : Γ) (v : Fin a → V) : Fin a → V :=
  fun b => act (x b) γ (v b)

def appL (a₁ a₂ : ℕ) : ((Fin a₁ → V) × (Fin a₂ → V)) →ₗ[O] (Fin (a₁ + a₂) → V) where
  toFun p := Fin.append p.1 p.2
  map_add' p q := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp
  map_smul' c p := by
    funext j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp

def resL₁ (a₁ a₂ : ℕ) : (Fin (a₁ + a₂) → V) →ₗ[O] (Fin a₁ → V) where
  toFun v := fun j => v (Fin.castAdd a₂ j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def resL₂ (a₁ a₂ : ℕ) : (Fin (a₁ + a₂) → V) →ₗ[O] (Fin a₂ → V) where
  toFun v := fun j => v (Fin.natAdd a₁ j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem resL₁_append {a₁ a₂ : ℕ} (v₁ : Fin a₁ → V) (v₂ : Fin a₂ → V) :
    resL₁ (O := O) a₁ a₂ (Fin.append v₁ v₂) = v₁ := by
  funext j; simp [resL₁]

theorem resL₂_append {a₁ a₂ : ℕ} (v₁ : Fin a₁ → V) (v₂ : Fin a₂ → V) :
    resL₂ (O := O) a₁ a₂ (Fin.append v₁ v₂) = v₂ := by
  funext j; simp [resL₂]

theorem blk_append (act : ι → Γ → V → V) {a₁ a₂ : ℕ} (x₁ : Fin a₁ → ι) (x₂ : Fin a₂ → ι) (γ : Γ)
    (v₁ : Fin a₁ → V) (v₂ : Fin a₂ → V) :
    blk act (Fin.append x₁ x₂) γ (Fin.append v₁ v₂) = Fin.append (blk act x₁ γ v₁) (blk act x₂ γ v₂) := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp [blk]

theorem append_sub {a₁ a₂ : ℕ} (u₁ v₁ : Fin a₁ → V) (u₂ v₂ : Fin a₂ → V) :
    Fin.append u₁ u₂ - Fin.append v₁ v₂ = Fin.append (u₁ - v₁) (u₂ - v₂) := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;> simp

def HasPres (act : ι → Γ → V → V) (W : Γ → Q → Q) (gl : G → Γ) (out : Q → C) (S : Set (G → C)) : Prop :=
  ∃ (a : ℕ) (x : Fin a → ι) (E : Fin a → V) (Y : Submodule O (Fin a → V)), Y.FG ∧
    ∃ (hst : ∀ γ : Γ, ∀ y ∈ Y, blk act x γ y ∈ Y) (hE : ∀ γ : Γ, blk act x γ E - E ∈ Y),
      ∀ c ∈ S, ∃ φ : ↥Y →ₗ[O] Q, (∀ (γ : Γ) (y : ↥Y), φ ⟨_, hst γ y.1 y.2⟩ = W γ (φ y)) ∧
        c = fun g => out (φ ⟨_, hE (gl g)⟩)

variable (act : ι → Γ → V → V) (W : Γ → Q → Q) (gl : G → Γ) (out : Q → C)

theorem hasPres_empty : HasPres (O := O) act W gl out ∅ := by
  refine ⟨0, Fin.elim0, 0, ⊥, Submodule.fg_bot, ?_, ?_, ?_⟩
  · intro γ y _
    rw [Subsingleton.elim (blk act Fin.elim0 γ y) 0]; exact Submodule.zero_mem _
  · intro γ
    rw [Subsingleton.elim (blk act Fin.elim0 γ 0 - 0) 0]; exact Submodule.zero_mem _
  · intro c hc; exact absurd hc (Set.notMem_empty c)

theorem hasPres_union {S T : Set (G → C)} (hS : HasPres (O := O) act W gl out S)
    (hT : HasPres (O := O) act W gl out T) : HasPres (O := O) act W gl out (S ∪ T) := by
  obtain ⟨a₁, x₁, E₁, Y₁, hY₁, hst₁, hE₁, hφ₁⟩ := hS
  obtain ⟨a₂, x₂, E₂, Y₂, hY₂, hst₂, hE₂, hφ₂⟩ := hT
  set Y : Submodule O (Fin (a₁ + a₂) → V) := (Y₁.prod Y₂).map (appL a₁ a₂) with hYdef
  have mem_of : ∀ y₁ ∈ Y₁, ∀ y₂ ∈ Y₂, Fin.append y₁ y₂ ∈ Y := fun y₁ h₁ y₂ h₂ =>
    Submodule.mem_map_of_mem (f := appL a₁ a₂) (p := Y₁.prod Y₂) (r := (y₁, y₂)) (Submodule.mem_prod.2 ⟨h₁, h₂⟩)
  have mem_iff : ∀ y ∈ Y, ∃ y₁ ∈ Y₁, ∃ y₂ ∈ Y₂, y = Fin.append y₁ y₂ := by
    intro y hy
    obtain ⟨⟨y₁, y₂⟩, ⟨h₁, h₂⟩, rfl⟩ := Submodule.mem_map.1 hy
    exact ⟨y₁, h₁, y₂, h₂, rfl⟩
  have r₁ : ∀ y ∈ Y, resL₁ (O := O) a₁ a₂ y ∈ Y₁ := by
    intro y hy
    obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := mem_iff y hy
    rw [resL₁_append]; exact h₁
  have r₂ : ∀ y ∈ Y, resL₂ (O := O) a₁ a₂ y ∈ Y₂ := by
    intro y hy
    obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := mem_iff y hy
    rw [resL₂_append]; exact h₂
  have hst : ∀ γ : Γ, ∀ y ∈ Y, blk act (Fin.append x₁ x₂) γ y ∈ Y := by
    intro γ y hy
    obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := mem_iff y hy
    rw [blk_append]
    exact mem_of _ (hst₁ γ y₁ h₁) _ (hst₂ γ y₂ h₂)
  have hEq : ∀ γ : Γ, blk act (Fin.append x₁ x₂) γ (Fin.append E₁ E₂) - Fin.append E₁ E₂ =
      Fin.append (blk act x₁ γ E₁ - E₁) (blk act x₂ γ E₂ - E₂) := by
    intro γ; rw [blk_append, append_sub]
  have hE : ∀ γ : Γ, blk act (Fin.append x₁ x₂) γ (Fin.append E₁ E₂) - Fin.append E₁ E₂ ∈ Y := by
    intro γ; rw [hEq]; exact mem_of _ (hE₁ γ) _ (hE₂ γ)
  refine ⟨a₁ + a₂, Fin.append x₁ x₂, Fin.append E₁ E₂, Y, ?_, hst, hE, ?_⟩
  · exact (hY₁.prod hY₂).map _
  · intro c hc
    rcases hc with hc | hc
    · obtain ⟨φ, hφ, rfl⟩ := hφ₁ c hc
      let ρ : ↥Y →ₗ[O] ↥Y₁ := ((resL₁ (O := O) a₁ a₂).domRestrict Y).codRestrict Y₁ (fun y => r₁ y.1 y.2)
      refine ⟨φ ∘ₗ ρ, ?_, ?_⟩
      · intro γ y
        obtain ⟨y, hy⟩ := y
        obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := mem_iff y hy
        have e1 : (ρ ⟨_, hst γ _ hy⟩ : ↥Y₁) = ⟨_, hst₁ γ y₁ h₁⟩ := by
          apply Subtype.ext
          show resL₁ (O := O) a₁ a₂ (blk act (Fin.append x₁ x₂) γ (Fin.append y₁ y₂)) = _
          rw [blk_append, resL₁_append]
        have e2 : (ρ ⟨_, hy⟩ : ↥Y₁) = ⟨y₁, h₁⟩ := by
          apply Subtype.ext
          show resL₁ (O := O) a₁ a₂ (Fin.append y₁ y₂) = _
          rw [resL₁_append]
        simp only [LinearMap.comp_apply]
        rw [e1, e2]
        exact hφ γ ⟨y₁, h₁⟩
      · funext g
        simp only [LinearMap.comp_apply]
        congr 2
        apply Subtype.ext
        show _ = resL₁ (O := O) a₁ a₂ (blk act (Fin.append x₁ x₂) (gl g) (Fin.append E₁ E₂) - Fin.append E₁ E₂)
        rw [hEq, resL₁_append]
    · obtain ⟨φ, hφ, rfl⟩ := hφ₂ c hc
      let ρ : ↥Y →ₗ[O] ↥Y₂ := ((resL₂ (O := O) a₁ a₂).domRestrict Y).codRestrict Y₂ (fun y => r₂ y.1 y.2)
      refine ⟨φ ∘ₗ ρ, ?_, ?_⟩
      · intro γ y
        obtain ⟨y, hy⟩ := y
        obtain ⟨y₁, h₁, y₂, h₂, rfl⟩ := mem_iff y hy
        have e1 : (ρ ⟨_, hst γ _ hy⟩ : ↥Y₂) = ⟨_, hst₂ γ y₂ h₂⟩ := by
          apply Subtype.ext
          show resL₂ (O := O) a₁ a₂ (blk act (Fin.append x₁ x₂) γ (Fin.append y₁ y₂)) = _
          rw [blk_append, resL₂_append]
        have e2 : (ρ ⟨_, hy⟩ : ↥Y₂) = ⟨y₂, h₂⟩ := by
          apply Subtype.ext
          show resL₂ (O := O) a₁ a₂ (Fin.append y₁ y₂) = _
          rw [resL₂_append]
        simp only [LinearMap.comp_apply]
        rw [e1, e2]
        exact hφ γ ⟨y₂, h₂⟩
      · funext g
        simp only [LinearMap.comp_apply]
        congr 2
        apply Subtype.ext
        show _ = resL₂ (O := O) a₁ a₂ (blk act (Fin.append x₁ x₂) (gl g) (Fin.append E₁ E₂) - Fin.append E₁ E₂)
        rw [hEq, resL₂_append]

theorem hasPres_finset (F : Finset (G → C)) (h : ∀ c ∈ F, HasPres (O := O) act W gl out {c}) :
    HasPres (O := O) act W gl out (F : Set (G → C)) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using hasPres_empty (O := O) act W gl out
  | insert c F hc ih =>
    rw [Finset.coe_insert, Set.insert_eq]
    exact hasPres_union act W gl out (h c (Finset.mem_insert_self c F))
      (ih fun c' hc' => h c' (Finset.mem_insert_of_mem hc'))

end GlobalTheory.Pass.LocDual.OneX.Combine

end

namespace GlobalTheory.Pass.LocDual.OneX

open GlobalTheory.Pass.LocDual.OneX.Combine in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem cutCoc_finset_common : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (F : Finset (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)),
    (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ⊆
    cutCoc i w hw r Xs M →
    ∃ (a : ℕ) (x : Fin a → ↥Xs) (E : Fin a → Fin D.R.nV → KK D.nd i)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)), Y.FG ∧
    ∃ (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) (hE : ∀ γ : GE D.nd, actK i r Xs x γ E - E ∈ Y),
    ∀ c ∈ F, ∃ φ : ↥Y →ₗ[D.nd.O i] KOG (D.nd.O i) k,
    (∀ (γ : GE D.nd) (y : ↥Y), φ ⟨_, hst γ y.1 y.2⟩ = WKG M γ (φ y)) ∧
    c = fun g => Br.phi (D.nbr i w hw) k (φ ⟨_, hE (gl i w hw g)⟩) := by
  intro D i w hw r Xs k M F hF
  have h := hasPres_finset (O := D.nd.O i)
    (fun (x : ↥Xs) (γ : GE D.nd) (v : Fin D.R.nV → KK D.nd i) => (mapM (toK D.nd i) (rTwO D.nd i r x) γ).mulVec v)
    (fun γ q => WKG M γ q) (gl i w hw) (Br.phi (D.nbr i w hw) k) F ?_
  · exact h
  · intro c hc
    obtain ⟨a, x, hx, E, Y, hY, hst, hE, φ, hφ, rfl⟩ := hF (Finset.mem_coe.2 hc)
    refine ⟨a, fun j => ⟨x j, hx j⟩, E, Y, hY, hst, hE, ?_⟩
    intro c' hc'
    rw [Set.mem_singleton_iff] at hc'
    subst hc'
    exact ⟨φ, hφ, rfl⟩

end GlobalTheory.Pass.LocDual.OneX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamRepresentationTensorComparison
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.ExactMult

theorem finrank_add_of_exact {L A₀ A₁ A₂ : Type} [Field L] [AddCommGroup A₀] [Module L A₀]
    [AddCommGroup A₁] [Module L A₁] [AddCommGroup A₂] [Module L A₂] (i : A₀ →ₗ[L] A₁) (p : A₁ →ₗ[L] A₂)
    (hi : Function.Injective i) (hk : LinearMap.range i = LinearMap.ker p)
    (S₀ : Submodule L A₀) (S₁ : Submodule L A₁) (S₂ : Submodule L A₂) [FiniteDimensional L S₁]
    (h0 : S₀ = S₁.comap i) (h2 : S₁.map p = S₂) :
    finrank L S₁ = finrank L S₀ + finrank L S₂ := by
  have e := LinearMap.finrank_range_add_finrank_ker (p.domRestrict S₁)
  rw [LinearMap.range_domRestrict, h2, LinearMap.ker_domRestrict, ← hk] at e
  have e1 : finrank L ((LinearMap.range i).comap S₁.subtype) = finrank L S₀ := by
    rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, h0,
      (Submodule.equivMapOfInjective i hi (S₁.comap i)).finrank_eq, Submodule.map_comap_eq, inf_comm]
  omega

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem mem_fil (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) (x : V ⊗[Qp] BdR) :
    x ∈ FildR PD ρ τ a ↔ ((∀ g, actVdR PD ρ g x = x) ∧
      ∀ c : K, mulVdR (LL := LL) (V := V) c x = τ c • x) ∧ x ∈ FilV PD (LL := LL) (V := V) a := by
  simp only [FildR, DdRE, DdR, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero]

theorem map_mul (f : V →ₗ[LL] V') (c : K) (x : V ⊗[Qp] BdR) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (mulVdR (LL := LL) (V := V) c x) =
      mulVdR (LL := LL) (V := V') c (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [mulVdR]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem map_act (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (he : ∀ g v, f (ρ g v) = ρ' g (f v)) (g : G) (x : V ⊗[Qp] BdR) :
    AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) (actVdR PD ρ g x) =
      actVdR PD ρ' g (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVdR, he]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem act_mul (ρ : Representation LL G V) (g : G) (c : K) (x : V ⊗[Qp] BdR) :
    actVdR PD ρ g (mulVdR (LL := LL) (V := V) c x) =
      mulVdR (LL := LL) (V := V) c (actVdR PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVdR, mulVdR]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem mul_mem_filV (a : ℤ) (c : K) (x : V ⊗[Qp] BdR) (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    mulVdR (LL := LL) (V := V) c x ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    refine ⟨v ⊗ₜ ⟨c • b.1, (PD.Fil a).smul_mem c b.2⟩, ?_⟩
    simp [mulVdR, Algebra.smul_def]
  | add y z hy hz => rw [map_add, map_add]; exact Submodule.add_mem _ hy hz

noncomputable def ev (x : V ⊗[Qp] BdR) : LL ⊗[Qp] K →ₗ[Qp] V ⊗[Qp] BdR :=
  TensorProduct.lift (LinearMap.mk₂ Qp (fun (c : LL) (k : K) => c • mulVdR (LL := LL) (V := V) k x)
    (fun _ _ _ => add_smul _ _ _) (fun _ _ _ => smul_assoc _ _ _)
    (fun c k k' => by
      rw [← smul_add]
      congr 1
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [mulVdR, add_mul, tmul_add]
      | add y z hy hz => simp only [map_add, hy, hz]; abel)
    (fun q c k => by
      rw [smul_comm q c]
      congr 1
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v b =>
        have : algebraMap K BdR (q • k) * b = q • (algebraMap K BdR k * b) := by
          rw [← Algebra.smul_def, ← Algebra.smul_def, smul_assoc]
        simp only [mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply, this,
          tmul_smul]
      | add y z hy hz => simp only [map_add, hy, hz, smul_add]))

theorem ev_tmul (x : V ⊗[Qp] BdR) (c : LL) (k : K) :
    ev (LL := LL) (K := K) x (c ⊗ₜ k) = c • mulVdR (LL := LL) (V := V) k x := rfl

theorem mul_mul (y k : K) (x : V ⊗[Qp] BdR) :
    mulVdR (LL := LL) (V := V) (y * k) x = mulVdR (LL := LL) (V := V) y (mulVdR (LL := LL) (V := V) k x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [mulVdR, mul_assoc]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem map_fildR_eq [CharZero Qp] (ρ : Representation LL G V) (ρ' : Representation LL G V')
    (f : V →ₗ[LL] V') (he : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) (a : ℤ)
    (hs : ∀ y ∈ DdR PD ρ' ⊓ FilV PD (LL := LL) (V := V') a,
      ∃ x ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a,
        AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR) x = y) :
    (FildR PD ρ τ a).map (AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)) =
      FildR PD ρ' τ a := by
  haveI := PD.finK
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := (mem_fil PD ρ τ a x).1 hx
    refine (mem_fil PD ρ' τ a _).2 ⟨⟨fun g => ?_, fun c => ?_⟩, GlobalTheory.HTW.map_mem_FilV PD f a x h3⟩
    · rw [← map_act PD ρ ρ' f he, h1]
    · rw [← map_mul, h2, map_smul]
  · intro y hy
    obtain ⟨x, ⟨hx1, hx2⟩, rfl⟩ := hs y ⟨hy.1.1, hy.2⟩
    obtain ⟨⟨-, h2⟩, -⟩ := (mem_fil PD ρ' τ a _).1 hy
    have h1 : ∀ g, actVdR PD ρ g x = x := by
      simpa only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] using hx1
    obtain ⟨m, c, k, hc, hk⟩ := GlobalTheory.exists_embedding_idempotent_tensor Qp K LL τ
    refine ⟨∑ j, c j • mulVdR (LL := LL) (V := V) (k j) x,
      (mem_fil PD ρ τ a _).2 ⟨⟨fun g => ?_, fun y => ?_⟩, ?_⟩, ?_⟩
    · simp only [map_sum, map_smul, act_mul, h1]
    · have := congrArg (ev (LL := LL) (K := K) x) (hk y)
      simp only [map_sum, ev_tmul, mul_mul] at this
      simp only [map_sum, map_smul, this, Finset.smul_sum, mul_smul]
    · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (mul_mem_filV PD a _ x hx2)
    · simp only [map_sum, map_smul, map_mul, h2, ← mul_smul, ← Finset.sum_smul, hc, one_smul]

variable {V₀ : Type} [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]

theorem tensor_exact (ι : V₀ →ₗ[LL] V) (π : V →ₗ[LL] V') (hι : Function.Injective ι)
    (hπ : Function.Surjective π) (hk : LinearMap.range ι = LinearMap.ker π) :
    Function.Injective (AlgebraTensorModule.map ι (LinearMap.id : BdR →ₗ[Qp] BdR)) ∧
      LinearMap.range (AlgebraTensorModule.map ι (LinearMap.id : BdR →ₗ[Qp] BdR)) =
        LinearMap.ker (AlgebraTensorModule.map π (LinearMap.id : BdR →ₗ[Qp] BdR)) := by
  have e1 : ∀ x, AlgebraTensorModule.map ι (LinearMap.id : BdR →ₗ[Qp] BdR) x =
      (ι.restrictScalars Qp).rTensor BdR x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add y z hy hz => simp only [map_add, hy, hz]
  have e2 : ∀ x, AlgebraTensorModule.map π (LinearMap.id : BdR →ₗ[Qp] BdR) x =
      (π.restrictScalars Qp).rTensor BdR x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add y z hy hz => simp only [map_add, hy, hz]
  have hex : Function.Exact (ι.restrictScalars Qp) (π.restrictScalars Qp) :=
    (LinearMap.exact_iff.2 hk.symm : Function.Exact ι π)
  constructor
  · intro x y h
    rw [e1, e1] at h
    exact Module.Flat.rTensor_preserves_injective_linearMap (M := BdR) (ι.restrictScalars Qp) hι h
  · ext x
    have := rTensor_exact BdR hex hπ x
    simp only [LinearMap.mem_range, LinearMap.mem_ker, e1, e2]
    exact this.symm

end General

theorem exact_hodge_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V₀ : Type) [AddCommGroup V₀] [Module ↥LL.1 V₀] [Module ℚ_[l] V₀] [IsScalarTower ℚ_[l] ↥LL.1 V₀] [FiniteDimensional ↥LL.1 V₀] (ρ₀ : Representation ↥LL.1 ↥(GK K) V₀) (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (ι : V₀ →ₗ[↥LL.1] V₁) (π : V₁ →ₗ[↥LL.1] V₂), (∀ g x, ι (ρ₀ g x) = ρ₁ g (ι x)) → (∀ g x, π (ρ₁ g x) = ρ₂ g (π x)) → Function.Injective ι → Function.Surjective π → LinearMap.range ι = LinearMap.ker π → IsDR (P.PD K) ρ₁ → IsDR (P.PD K) ρ₀ ∧ IsDR (P.PD K) ρ₂ ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), finrank ↥LL.1 ↥(FildR (P.PD K) ρ₁ τ a) = finrank ↥LL.1 ↥(FildR (P.PD K) ρ₀ τ a) + finrank ↥LL.1 ↥(FildR (P.PD K) ρ₂ τ a) ∧ multV (P.PD K) ρ₁ τ a = multV (P.PD K) ρ₀ τ a + multV (P.PD K) ρ₂ τ a ∧ (IsJumpV (P.PD K) ρ₁ τ a ↔ IsJumpV (P.PD K) ρ₀ τ a ∨ IsJumpV (P.PD K) ρ₂ τ a) := by
  intro l _ P AI T K LL V₀ _ _ _ _ _ ρ₀ V₁ _ _ _ _ _ ρ₁ V₂ _ _ _ _ _ ρ₂ ι π hι hπ hi hs hk hd
  obtain ⟨d2, hst⟩ := (GlobalTheory.T.deRham_subrep_quotient_and_strictness l P AI T K LL V₁ ρ₁ V₂ ρ₂ π hπ).2 hs hd
  obtain ⟨t1, t2⟩ := tensor_exact (Qp := ℚ_[l]) (BdR := P.R.BdR) ι π hi hs hk
  have hf : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), finrank ↥LL.1 ↥(FildR (P.PD K) ρ₁ τ a) =
      finrank ↥LL.1 ↥(FildR (P.PD K) ρ₀ τ a) + finrank ↥LL.1 ↥(FildR (P.PD K) ρ₂ τ a) := by
    intro τ a
    haveI := (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL V₁ ρ₁ τ a).1
    exact finrank_add_of_exact _ _ t1 t2 _ _ _ (GlobalTheory.HTW.FildR_eq_comap (P.PD K) ρ₀ ρ₁ ι hi hι τ a)
      (map_fildR_eq (P.PD K) ρ₁ ρ₂ π hπ τ a (hst a))
  refine ⟨(GlobalTheory.T.deRham_subrep_quotient_and_strictness l P AI T K LL V₀ ρ₀ V₁ ρ₁ ι hι).1 hi hd, d2, fun τ a => ?_⟩
  have hm : multV (P.PD K) ρ₁ τ a = multV (P.PD K) ρ₀ τ a + multV (P.PD K) ρ₂ τ a := by
    unfold multV
    rw [hf τ a, hf τ (a + 1)]
    push_cast
    ring
  refine ⟨hf τ a, hm, ?_⟩
  obtain ⟨-, n0, j0⟩ := GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL V₀ ρ₀ τ a
  obtain ⟨-, -, j1⟩ := GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL V₁ ρ₁ τ a
  obtain ⟨-, n2, j2⟩ := GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l P AI T K LL V₂ ρ₂ τ a
  rw [j0, j1, j2, hm]
  omega

end GlobalTheory.Per.ExactMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerFamilySingleEqMul
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem ofW_single : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (i n : ℕ) (c : Wq l a), ofW t K e (Pi.single (i, n) c) = cstW t K c * uFam a K ^ (n % e) * dFam a K e (n / e) * xFam a K i := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t i n c
  funext τ
  have hR : (cstW t K c * uFam a K ^ (n % e) * dFam a K e (n / e) * xFam a K i) τ
      = C (C (algebraMap O K (emb t τ c) / (dpDen e i n : K)) * X ^ n) * X ^ i := by
    simp only [Pi.mul_apply, Pi.pow_apply, cstW, uFam, dFam, xFam]
    have h1 : (X : K⟦X⟧) ^ n = X ^ (n % e) * X ^ (e * (n / e)) := by
      rw [← pow_add, Nat.mod_add_div]
    rw [h1, dpDen, Nat.cast_mul, div_eq_mul_inv, mul_inv]
    simp only [map_mul, map_pow]
    ring
  rw [hR]
  ext i' n'
  rw [coeff_ofW, coeff_C_mul, coeff_X_pow, Pi.single_apply]
  by_cases hi : i' = i
  · subst hi
    by_cases hn : n' = n
    · subst hn
      simp [coeff_C_mul, coeff_X_pow]
    · simp [coeff_C_mul, coeff_X_pow, hn]
  · simp [hi]

end GlobalTheory.CrysPrism
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedPowerSeriesGeneratorSetEqSumAddMul
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem sdSet_eq_sum_add_mul (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) :
    ∀ F ∈ SdSet t K e, ∃ (N : ℕ) (v : ℕ → Wq l a), ∃ y ∈ SdSet t K e,
      F = ∑ n ∈ Finset.range N, cstS t K (v n) * dpS a e n + (l : ZMod a → K⟦X⟧) * y := by
  rintro F ⟨w, hw, hF⟩
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl0 : (l : Wq l a) ≠ 0 := by
    have h := WittVector.p_nonzero l (Fq l a)
    exact h
  have h1 := hw 1
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop] at h1
  obtain ⟨N, hN⟩ := h1
  have h2 : ∀ n, ∃ z : Wq l a, (n < N → z = 0) ∧ (¬ n < N → w n = l * z) := by
    intro n
    by_cases h : n < N
    · exact ⟨0, fun _ => rfl, fun h' => absurd h h'⟩
    · obtain ⟨z, hz⟩ := hN n (not_lt.1 h)
      exact ⟨z, fun h' => absurd h' h, fun _ => by rw [hz, pow_one]⟩
  choose z hz0 hz using h2
  have hfac : ∀ n : ℕ, ((n / e).factorial : K) ≠ 0 := fun n => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  refine ⟨N, w, fun τ => PowerSeries.mk fun n => ((n / e).factorial : K)⁻¹ * algebraMap O K (emb t τ (z n)),
    ⟨z, fun r => ?_, fun τ n => ?_⟩, ?_⟩
  · filter_upwards [hw (r + 1)] with n hn
    by_cases h : n < N
    · rw [hz0 n h]; exact dvd_zero _
    · rw [hz n h, pow_succ'] at hn
      exact (mul_dvd_mul_iff_left hl0).1 hn
  · rw [coeff_mk, mul_inv_cancel_left₀ (hfac n)]
  · funext τ
    ext m
    apply mul_left_cancel₀ (hfac m)
    rw [hF]
    have hc : (l : K⟦X⟧) = C (l : K) := (map_natCast (C : K →+* K⟦X⟧) l).symm
    simp only [Pi.add_apply, Finset.sum_apply, Pi.mul_apply, Pi.natCast_apply, map_add, map_sum, cstS_apply, dpS,
      hc, coeff_C_mul, coeff_monomial, coeff_mk, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
    by_cases h : m < N
    · rw [if_pos h, hz0 m h, map_zero, map_zero]
      field_simp [hfac m]
      ring
    · rw [if_neg h, hz m h, map_mul, map_mul, map_natCast, map_natCast]
      field_simp [hfac m]
      ring

end GlobalTheory.CrysPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedTwoVariableSubringSubsetGeneratorSetStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedTwoVariableSubring_subset_generatorSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ F ∈ PPd t K e, F ∈ PPSet t K e := by
  first | exact @GlobalTheory.CrysPrism.PPd_subset_PPSet | exact GlobalTheory.CrysPrism.PPd_subset_PPSet | (intros; apply GlobalTheory.CrysPrism.PPd_subset_PPSet <;> assumption)
end

