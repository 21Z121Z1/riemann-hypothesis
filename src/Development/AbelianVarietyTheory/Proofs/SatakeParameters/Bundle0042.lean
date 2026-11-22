import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.RootMultiplicityCancellation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0040
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveProdQuotientOfMemAnnihilatorKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0549
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsSepClosedResidueFieldPowerSeriesComplex
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdmissibleBranchingIffIsBranching
section
noncomputable section

namespace GlobalTheory.InertialTypesCmp

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open Formalism.MainNotions.SumRepresentations.At GlobalTheory.IndefiniteRowSideFullHecke.InertiaTypeCancellation

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def ClauseQ : Prop :=
  ∀ (i : N.Loc) (P : A.AV i) (w : PlE H), (w ∈ N.S i ∨ w ∈ N.Q i) →
    (w ∈ N.Q i ∨ (Del N i ∧ (w ∈ placesOver H.E H.pde ∨ (N.l i = H.pde ∧ w ∈ placesOver H.E H.pde')))) →
    A.mono0 (A.locV i P w) ∧ ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
      A.inePol (A.locV i P w) σ = (X - 1) ^ R.r * (X - C (iotaO N A i (chi1 N i σ))) ^ R.t

def ClauseG : Prop :=
  ∀ (i : N.Loc) (P : A.AV i) (w : PlE H), w ∈ N.S i → (∃ k, w ∈ placesOver H.E (H.g k)) →
    TameGen N (N.plOm.1 w) (N.gam0 i w) →
    (A.inePol (A.locV i P w) (N.gam0 i w)).rootMultiplicity (iotaO N A i (chi1 N i (N.gam0 i w))) ≤ R.t →
    ∃ a b : A.LP w, A.locV i P w = A.lpSum a b ∧ A.lpDim a = R.r ∧ A.lpDim b = R.t ∧ A.mono0 b ∧
      ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol b σ = (X - C (iotaO N A i (chi1 N i σ))) ^ R.t

def ClauseC : Prop := ∀ w (a b c : A.LP w), A.lpSum a c = A.lpSum b c → a = b

def Rest : Prop :=
  ∀ (i : N.Loc) (P : A.AV i) (k : Fin 2) (w : PlE H), w ∈ placesOver H.E (H.g k) →
    w ∉ placesOver H.E (N.l i) →
    (A.inePol (A.locV i P w) (N.gam0 i w)).rootMultiplicity (chiC N A i (N.gam0 i w)) ≤ R.t →
    A.lpDim (A.locV i P w) = R.nV ∧
    (A.inePol (A.locV i P w) (N.gam0 i w) = 0 →
      ∃ a b : A.LP w, A.locV i P w = A.lpSum a b ∧ A.lpDim b = R.t ∧ HasInertia N A i w b 0 R.t)

def Regular : Prop :=
  ∀ (i : N.Loc) (P : A.AV i) (k : Fin 2) (w : PlE H), w ∈ placesOver H.E (H.g k) →
    w ∉ placesOver H.E (N.l i) →
    A.lpDim (A.locV i P w) = R.nV ∧ A.inePol (A.locV i P w) (N.gam0 i w) ≠ 0

open NumberField IsDedekindDomain Polynomial in
variable {R : _root_.Formalism.BasicNotions.Ranks} {H : _root_.Formalism.BasicNotions.Host R} {what₂ : _root_.Formalism.BasicNotions.Rows.Data R} (N : _root_.Formalism.BasicNotions.NData R H what₂) (A : _root_.Formalism.BasicNotions.NAut N) in
private theorem lpDim_foldr_lpSum_eq_sum_map {α : Type*} {w : _root_.Formalism.BasicNotions.PlE H}
    (f : α → A.LP w) (l : List α) :
    A.lpDim (l.foldr (fun k acc => A.lpSum (f k) acc) (A.lpZero w)) =
      (l.map fun k => A.lpDim (f k)).sum := by
  induction l with
  | nil => simp [_root_.Formalism.BasicNotions.NAut.lpDim_zero]
  | cons k l ih => simp [_root_.Formalism.BasicNotions.NAut.lpDim_sum, ih]

open NumberField IsDedekindDomain Polynomial in
variable {R : _root_.Formalism.BasicNotions.Ranks} {H : _root_.Formalism.BasicNotions.Host R} {what₂ : _root_.Formalism.BasicNotions.Rows.Data R} (N : _root_.Formalism.BasicNotions.NData R H what₂) (A : _root_.Formalism.BasicNotions.NAut N) in
private theorem lpDim_foldr_lpSum_eq_length_mul_of_const {α : Type*} {w : _root_.Formalism.BasicNotions.PlE H}
    (f : α → A.LP w) (m : ℕ) (hf : ∀ k, A.lpDim (f k) = m) (l : List α) :
    A.lpDim (l.foldr (fun k acc => A.lpSum (f k) acc) (A.lpZero w)) = l.length * m := by
  induction l with
  | nil => simp [_root_.Formalism.BasicNotions.NAut.lpDim_zero]
  | cons k l ih => simp [_root_.Formalism.BasicNotions.NAut.lpDim_sum, hf, ih, add_mul, add_comm]

open NumberField IsDedekindDomain Polynomial in
variable {R : _root_.Formalism.BasicNotions.Ranks} {H : _root_.Formalism.BasicNotions.Host R} {what₂ : _root_.Formalism.BasicNotions.Rows.Data R} (N : _root_.Formalism.BasicNotions.NData R H what₂) (A : _root_.Formalism.BasicNotions.NAut N) in
private theorem lpDim_spehLoc_eq_mul (p : _root_.Formalism.BasicNotions.Part A.CG) (w : _root_.Formalism.BasicNotions.PlE H) :
    A.lpDim (_root_.Formalism.MainNotions.N.spehLoc N A p w) = p.a * p.d := by
  unfold _root_.Formalism.MainNotions.N.spehLoc
  rw [lpDim_foldr_lpSum_eq_length_mul_of_const N A _ p.a (fun k => by rw [_root_.Formalism.BasicNotions.NAut.lpDim_tw, _root_.Formalism.BasicNotions.NAut.locG_dim])]
  simp [mul_comm]

open NumberField IsDedekindDomain Polynomial in
variable {R : _root_.Formalism.BasicNotions.Ranks} {H : _root_.Formalism.BasicNotions.Host R} {what₂ : _root_.Formalism.BasicNotions.Rows.Data R} (N : _root_.Formalism.BasicNotions.NData R H what₂) (A : _root_.Formalism.BasicNotions.NAut N) in
theorem _root_.GlobalTheory.InertialTypesCmp.lpDim_isoLoc (P : List (_root_.Formalism.BasicNotions.Part A.CG)) (w : _root_.Formalism.BasicNotions.PlE H) :
    A.lpDim (_root_.Formalism.MainNotions.N.isoLoc N A P w) = _root_.Formalism.MainNotions.N.rankIso N A P := by
  unfold _root_.Formalism.MainNotions.N.isoLoc _root_.Formalism.MainNotions.N.rankIso
  rw [lpDim_foldr_lpSum_eq_sum_map]
  simp [lpDim_spehLoc_eq_mul]

end GlobalTheory.InertialTypesCmp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutomorphicRepEqOfEqAtAlmostAllSplitPlacesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicRep_eq_of_eq_at_almost_all_split_places : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i → ∀ P P' : A.AV i, (∀ᶠ w in Filter.cofinite, IsSplitPl H w → A.locV i P w = A.locV i P' w) → P = P' := by
  first | exact @GlobalTheory.RowTie.repDet_split | exact GlobalTheory.RowTie.repDet_split | (intros; apply GlobalTheory.RowTie.repDet_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardQuotMatrixRangeDvrEqResiduePowCorank
section
open GlobalTheory.LatHecke GlobalTheory.SatakeInv

namespace GlobalTheory.IdxRank

theorem mem_smul_top_of_forall_mem {O : Type} [CommRing O] (I : Ideal O) {r : ℕ}
    (z : Fin r → O) (hz : ∀ i, z i ∈ I) : z ∈ I • (⊤ : Submodule O (Fin r → O)) := by
  have h : z = ∑ i, z i • (Pi.single i (1 : O) : Fin r → O) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hz i) trivial

theorem card_quot_range (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] (r : ℕ) (A : Matrix (Fin r) (Fin r) O)
    (hA : IsLocalRing.maximalIdeal O • (⊤ : Submodule O (Fin r → O)) ≤
      LinearMap.range A.mulVecLin) :
    Nat.card ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) =
      qRes O ^ (r - (A.map (IsLocalRing.residue O)).rank) := by
  classical
  set F := IsLocalRing.ResidueField O with hF
  set res : O →+* F := IsLocalRing.residue O with hres
  set Ab : Matrix (Fin r) (Fin r) F := A.map res with hAb
  set R : Submodule F (Fin r → F) := LinearMap.range Ab.mulVecLin with hR
  let π : (Fin r → O) →ₗ[O] (Fin r → F) := (Algebra.linearMap O F).compLeft (Fin r)
  have hπ : ∀ x i, π x i = res (x i) := fun x i => rfl
  have hπs : Function.Surjective π := by
    intro y
    refine ⟨fun i => (IsLocalRing.residue_surjective (y i)).choose, ?_⟩
    ext i
    exact (IsLocalRing.residue_surjective (y i)).choose_spec
  have hπA : ∀ x, π (A.mulVec x) = Ab.mulVec (π x) := by
    intro x
    ext i
    have h2 : π x = res ∘ x := rfl
    rw [h2, hπ]
    exact RingHom.map_mulVec res A x i
  let φ : (Fin r → O) →ₗ[O] ((Fin r → F) ⧸ R) := (R.mkQ.restrictScalars O).comp π
  have hφs : Function.Surjective φ :=
    (Submodule.mkQ_surjective R).comp hπs
  have hker : LinearMap.ker φ = LinearMap.range A.mulVecLin := by
    ext x
    constructor
    · intro hx
      have hx' : π x ∈ R := by
        have : R.mkQ (π x) = 0 := hx
        simpa using this
      obtain ⟨y, hy⟩ := hx'
      obtain ⟨y', rfl⟩ := hπs y
      have hy2 : π (A.mulVec y') = π x := by
        rw [hπA]; exact hy
      have hz : x - A.mulVec y' ∈ LinearMap.range A.mulVecLin := by
        apply hA
        apply mem_smul_top_of_forall_mem
        intro i
        have h1 : π (x - A.mulVec y') i = 0 := by
          rw [map_sub, hy2, sub_self]; rfl
        rw [hπ] at h1
        exact (IsLocalRing.residue_eq_zero_iff _).1 h1
      have : x = (x - A.mulVec y') + A.mulVecLin y' := by
        simp
      rw [this]
      exact Submodule.add_mem _ hz ⟨y', rfl⟩
    · rintro ⟨y, rfl⟩
      show R.mkQ (π (A.mulVec y)) = 0
      rw [hπA]
      simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨π y, rfl⟩
  have e : ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) ≃ ((Fin r → F) ⧸ R) :=
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans
      (φ.quotKerEquivOfSurjective hφs)).toEquiv
  rw [Nat.card_congr e]
  have hfin : Module.finrank F ((Fin r → F) ⧸ R) + Module.finrank F R = r := by
    have := Submodule.finrank_quotient_add_finrank R
    simpa using this
  have hrank : Ab.rank = Module.finrank F R := rfl
  have hdim : Module.finrank F ((Fin r → F) ⧸ R) = r - Ab.rank := by
    omega
  have : Finite ((Fin r → F) ⧸ R) := Finite.of_surjective R.mkQ (Submodule.mkQ_surjective R)
  rw [Module.natCard_eq_pow_finrank (K := F), hdim]
  rfl

end GlobalTheory.IdxRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EtaleFiniteStrictHenselianSplit
section
open IsLocalRing TensorProduct

namespace GlobalTheory.StrictHenselSplit

theorem isFiniteSplit_of_finrank_eq (A : Type) [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (ResidueField A)] : ∀ (r : ℕ) (B : Type) [CommRing B] [Algebra A B]
    [Algebra.Etale A B] [Module.Finite A B], Module.finrank A B = r → Algebra.IsFiniteSplit A B := by
  intro r
  induction r with
  | zero =>
    intro B _ _ _ _ hr
    haveI : Module.Free A B := Module.free_of_flat_of_isLocalRing
    haveI : Subsingleton B := (Module.finrank_eq_zero_iff_of_free A B).1 hr
    exact .of_subsingleton_top
  | succ r ih =>
    intro B _ _ _ _ hr
    haveI : Module.Free A B := Module.free_of_flat_of_isLocalRing
    obtain ⟨m, ⟨f⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun (ResidueField A)
      (ResidueField A ⊗[A] B)
    have hm : m = r + 1 := by
      have h1 := Module.finrank_baseChange (R := ResidueField A) (S := A) (M' := B)
      rw [f.toLinearEquiv.finrank_eq, Module.finrank_fin_fun] at h1
      omega
    let φ₀ : B →ₐ[A] ResidueField A :=
      (((Pi.evalAlgHom (ResidueField A) (fun _ : Fin m => ResidueField A) ⟨0, by omega⟩).comp
        f.toAlgHom).restrictScalars A).comp Algebra.TensorProduct.includeRight
    obtain ⟨ε, -⟩ := (GlobalTheory.EtaleHensel.bijective_residue_comp A B A).2 φ₀
    obtain ⟨e, ⟨he, he1⟩, -⟩ := GlobalTheory.existsUnique_mem_annihilator_ker ε
    let g : B ≃ₐ[A] A × (B ⧸ Ideal.span {e}) :=
      AlgEquiv.ofBijective _ (GlobalTheory.bijective_prod_quotient_of_mem_annihilator_ker he he1)
    haveI : Algebra.Etale A (A × (B ⧸ Ideal.span {e})) := .of_equiv g
    haveI : Algebra.Etale A (B ⧸ Ideal.span {e}) := by
      algebraize [RingHom.snd A (B ⧸ Ideal.span {e})]
      have : IsScalarTower A (A × (B ⧸ Ideal.span {e})) (B ⧸ Ideal.span {e}) :=
        IsScalarTower.of_algebraMap_eq' rfl
      exact .comp A (A × (B ⧸ Ideal.span {e})) (B ⧸ Ideal.span {e})
    haveI : Module.Finite A (B ⧸ Ideal.span {e}) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ A (Ideal.span {e})).toLinearMap
        Ideal.Quotient.mk_surjective
    haveI : Module.Free A (B ⧸ Ideal.span {e}) := Module.free_of_flat_of_isLocalRing
    have hC : Module.finrank A (B ⧸ Ideal.span {e}) = r := by
      have := g.toLinearEquiv.finrank_eq
      rw [Module.finrank_prod, Module.finrank_self] at this
      omega
    obtain ⟨k, ⟨h⟩⟩ := (ih (B ⧸ Ideal.span {e}) hC).nonempty_algEquiv_fun
    have : Algebra.IsFiniteSplit A (Fin 1 ⊕ Fin k → A) := inferInstance
    exact .of_algEquiv ((AlgEquiv.sumArrowEquivProdArrow (Fin 1) (Fin k) A A).trans
      ((AlgEquiv.prodCongr (AlgEquiv.funUnique (ι := Fin 1) A A) h.symm).trans g.symm))

end GlobalTheory.StrictHenselSplit

theorem GlobalTheory.etale_finite_strictHenselian_split : ∀ (A B : Type) [CommRing A] [HenselianLocalRing A]
    [IsSepClosed (IsLocalRing.ResidueField A)] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    [Module.Finite A B], ∃ n : ℕ, Nonempty (B ≃ₐ[A] (Fin n → A)) := by
  intro A B _ _ _ _ _ _ _
  exact (GlobalTheory.StrictHenselSplit.isFiniteSplit_of_finrank_eq A _ B rfl).nonempty_algEquiv_fun

example : ∀ (A B : Type) [CommRing A] [HenselianLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)] [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.Finite A B], ∃ n : ℕ, Nonempty (B ≃ₐ[A] (Fin n → A)) := GlobalTheory.etale_finite_strictHenselian_split
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsConjDoubleBlockOfIsoSubspaces
section
open Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.DoubleBlock

open Matrix

variable {k Γ : Type} [Field k] [Group Γ] {a : ℕ}

theorem exists_emb (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) (hW : IsInv ρ W) :
    ∃ (σ : Γ →* GL (Fin (Module.finrank k W)) k) (φ : (Fin (Module.finrank k W) → k) ≃ₗ[k] W),
      ∀ g x, (φ ((σ g : Matrix _ _ k) *ᵥ x) : Fin a → k) = (ρ g : Matrix _ _ k) *ᵥ (φ x : Fin a → k) := by
  classical
  let φ : (Fin (Module.finrank k W) → k) ≃ₗ[k] W := (Module.finBasis k W).equivFun.symm
  let r : Γ → (W →ₗ[k] W) := fun g =>
    (Matrix.toLin' (ρ g : Matrix (Fin a) (Fin a) k)).restrict (p := W) (q := W) (fun v hv => hW g v hv)
  have hr : ∀ g v, (r g v : Fin a → k) = (ρ g : Matrix _ _ k) *ᵥ (v : Fin a → k) := fun g v => rfl
  let m : Γ →* Matrix (Fin (Module.finrank k W)) (Fin (Module.finrank k W)) k :=
    { toFun := fun g => LinearMap.toMatrix' (φ.symm.toLinearMap ∘ₗ r g ∘ₗ φ.toLinearMap)
      map_one' := by
        rw [← LinearMap.toMatrix'_id]
        congr 1
        apply LinearMap.ext
        intro x
        have : r 1 (φ x) = φ x := by
          apply Subtype.ext
          rw [hr]; simp
        simp [this]
      map_mul' := fun g h => by
        rw [← LinearMap.toMatrix'_comp]
        congr 1
        apply LinearMap.ext
        intro x
        have : r (g * h) (φ x) = r g (r h (φ x)) := by
          apply Subtype.ext
          rw [hr, hr, hr]; simp
        simp [this] }
  refine ⟨m.toHomUnits, φ, fun g x => ?_⟩
  have : ((m.toHomUnits g : Matrix _ _ k)) *ᵥ x = φ.symm (r g (φ x)) := by
    change LinearMap.toMatrix' (φ.symm.toLinearMap ∘ₗ r g ∘ₗ φ.toLinearMap) *ᵥ x = _
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  rw [this, LinearEquiv.apply_symm_apply, hr]

theorem exists_emb_sum (ρ : Γ →* GL (Fin a) k) {d u : ℕ} (σ : Γ →* GL (Fin d) k)
    (τ : Γ →* GL (Fin u) k) (f₁ : (Fin d → k) →ₗ[k] (Fin a → k))
    (f₂ : (Fin u → k) →ₗ[k] (Fin a → k)) (i₁ : Function.Injective f₁) (i₂ : Function.Injective f₂)
    (h₁ : ∀ g x, f₁ ((σ g : Matrix _ _ k) *ᵥ x) = (ρ g : Matrix _ _ k) *ᵥ f₁ x)
    (h₂ : ∀ g x, f₂ ((τ g : Matrix _ _ k) *ᵥ x) = (ρ g : Matrix _ _ k) *ᵥ f₂ x)
    (hd : Disjoint (LinearMap.range f₁) (LinearMap.range f₂)) :
    ∃ f : (Fin (d + u) → k) →ₗ[k] (Fin a → k), Function.Injective f ∧
      LinearMap.range f = LinearMap.range f₁ ⊔ LinearMap.range f₂ ∧
      ∀ g x, f ((SumRepresentations.At.sumRep σ τ g : Matrix _ _ k) *ᵥ x) = (ρ g : Matrix _ _ k) *ᵥ f x := by
  let s : (Fin (d + u) → k) ≃ₗ[k] (Fin d → k) × (Fin u → k) :=
    (LinearEquiv.funCongrLeft k k finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow _ _ k k)
  have hs : ∀ x, s x = (fun i => x (finSumFinEquiv (Sum.inl i)), fun i => x (finSumFinEquiv (Sum.inr i))) :=
    fun x => rfl
  refine ⟨(f₁.coprod f₂) ∘ₗ s.toLinearMap, ?_, ?_, fun g x => ?_⟩
  · have : Function.Injective (f₁.coprod f₂) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range _ _ hd,
        LinearMap.ker_eq_bot.2 i₁, LinearMap.ker_eq_bot.2 i₂, Submodule.prod_bot]
    exact this.comp s.injective
  · rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, LinearMap.range_coprod]
  · have key : s ((SumRepresentations.At.sumRep σ τ g : Matrix _ _ k) *ᵥ x) =
        ((σ g : Matrix _ _ k) *ᵥ (s x).1, (τ g : Matrix _ _ k) *ᵥ (s x).2) := by
      have hM : (SumRepresentations.At.sumRep σ τ g).val = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (σ g).val 0 0 (τ g).val) := rfl
      rw [hM, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, Matrix.fromBlocks_mulVec, hs, hs]
      ext i <;> simp [Function.comp_def]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, key, LinearMap.coprod_apply, h₁, h₂,
      Matrix.mulVec_add]

theorem exists_conj (ρ : Γ →* GL (Fin a) k) {n : ℕ} (τ : Γ →* GL (Fin n) k)
    (f : (Fin n → k) →ₗ[k] (Fin a → k)) (hi : Function.Injective f) (hs : LinearMap.range f = ⊤)
    (h : ∀ g x, f ((τ g : Matrix _ _ k) *ᵥ x) = (ρ g : Matrix _ _ k) *ᵥ f x) :
    ∃ (hn : n = a) (Pm : GL (Fin a) k), ∀ g,
      ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
        Matrix.reindex (finCongr hn) (finCongr hn) ((τ g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  classical
  let e := LinearEquiv.ofBijective f ⟨hi, LinearMap.range_eq_top.1 hs⟩
  have hn : n = a := by simpa using e.finrank_eq
  subst hn
  let Pm : GL (Fin n) k := ⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap,
    by rw [← LinearMap.toMatrix'_comp]; simp, by rw [← LinearMap.toMatrix'_comp]; simp⟩
  have hP : ∀ x, (Pm : Matrix _ _ k) *ᵥ x = f x := fun x => LinearMap.toMatrix'_mulVec _ _
  refine ⟨rfl, Pm, fun g => ?_⟩
  have : ρ g * Pm = Pm * τ g := by
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Units.val_mul, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hP, h]
  rw [mul_assoc, this, inv_mul_cancel_left]
  simp

theorem exists_conj_double : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W₁ W₂ : Submodule k (Fin a → k)), IsSSRep ρ → IsInv ρ W₁ → IsInv ρ W₂ → W₁ ≠ ⊥ → W₁ ⊓ W₂ = ⊥ → IsoSub ρ W₁ W₂ → ∃ (d u : ℕ) (σ : Γ →* GL (Fin d) k) (υ : Γ →* GL (Fin u) k) (h : d + d + u = a) (Pm : GL (Fin a) k), 0 < d ∧ ∀ g, ((Pm⁻¹ * ρ g * Pm : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) = Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) k) : Matrix (Fin (d + d + u)) (Fin (d + d + u)) k) := by
  intro k Γ _ _ a ρ W₁ W₂ hss h₁ h₂ hne hdis ⟨e, he⟩
  have h12 : IsInv ρ (W₁ ⊔ W₂) := by
    intro g v hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem_sup (h₁ g x hx) (h₂ g y hy)
  obtain ⟨U, hU, hc⟩ := hss _ h12
  obtain ⟨σ, φ, hφ⟩ := exists_emb ρ W₁ h₁
  obtain ⟨υ, ψ, hψ⟩ := exists_emb ρ U hU
  have r₁ : LinearMap.range (W₁.subtype ∘ₗ φ.toLinearMap) = W₁ := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have r₂ : LinearMap.range (W₂.subtype ∘ₗ (φ.trans e).toLinearMap) = W₂ := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have r₃ : LinearMap.range (U.subtype ∘ₗ ψ.toLinearMap) = U := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨f, fi, fr, hf⟩ := exists_emb_sum ρ σ σ (W₁.subtype ∘ₗ φ.toLinearMap)
    (W₂.subtype ∘ₗ (φ.trans e).toLinearMap) (W₁.injective_subtype.comp φ.injective)
    (W₂.injective_subtype.comp (φ.trans e).injective) (fun g x => hφ g x)
    (fun g x => by
      have := he g (φ x) (h₁ g _ (φ x).2)
      have h' : φ ((σ g : Matrix _ _ k) *ᵥ x) = ⟨_, h₁ g _ (φ x).2⟩ := Subtype.ext (hφ g x)
      change (e (φ ((σ g : Matrix _ _ k) *ᵥ x)) : Fin a → k) = _
      rw [h', this]
      rfl)
    (by rw [r₁, r₂]; exact disjoint_iff.2 hdis)
  rw [r₁, r₂] at fr
  obtain ⟨F, Fi, Fr, hF⟩ := exists_emb_sum ρ (SumRepresentations.At.sumRep σ σ) υ f (U.subtype ∘ₗ ψ.toLinearMap) fi
    (U.injective_subtype.comp ψ.injective) hf (fun g x => hψ g x)
    (by rw [fr, r₃]; exact hc.disjoint)
  rw [fr, r₃, hc.sup_eq_top] at Fr
  obtain ⟨hn, Pm, hP⟩ := exists_conj ρ _ F Fi Fr hF
  exact ⟨_, _, σ, υ, hn, Pm, Nat.pos_of_ne_zero (fun h0 => hne (Submodule.finrank_eq_zero.1 h0)), hP⟩

end GlobalTheory.DoubleBlock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomOfIsStrictHenselisation
section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing

noncomputable section
namespace GlobalTheory.NCyc.StrictLocLift

theorem lift_unique {R Q T : Type} [CommRing R] [CommRing Q] [CommRing T] [HenselianLocalRing T]
    (tQ : R →+* Q) (htQ : tQ.Etale) (b : R →+* T) (g₁ g₂ : Q →+* T)
    (h₁ : g₁.comp tQ = b) (h₂ : g₂.comp tQ = b)
    (h : (residue T).comp g₁ = (residue T).comp g₂) : g₁ = g₂ := by
  letI : Algebra R Q := tQ.toAlgebra
  letI : Algebra R T := b.toAlgebra
  haveI : Algebra.Etale R Q := htQ
  let G₁ : Q →ₐ[R] T := { g₁ with commutes' := fun r => DFunLike.congr_fun h₁ r }
  let G₂ : Q →ₐ[R] T := { g₂ with commutes' := fun r => DFunLike.congr_fun h₂ r }
  have := (GlobalTheory.EtaleHensel.bijective_residue_comp R Q T).1 (a₁ := G₁) (a₂ := G₂) (by
    ext q; exact DFunLike.congr_fun h q)
  ext q; exact DFunLike.congr_fun this q

theorem lift_exists {R Q T : Type} [CommRing R] [CommRing Q] [CommRing T] [HenselianLocalRing T]
    (tQ : R →+* Q) (htQ : tQ.Etale) (b : R →+* T) (ψ : Q →+* ResidueField T)
    (hψ : ψ.comp tQ = (residue T).comp b) :
    ∃ g : Q →+* T, g.comp tQ = b ∧ (residue T).comp g = ψ := by
  letI : Algebra R Q := tQ.toAlgebra
  letI : Algebra R T := b.toAlgebra
  haveI : Algebra.Etale R Q := htQ
  let Ψ : Q →ₐ[R] ResidueField T := { ψ with commutes' := fun r => DFunLike.congr_fun hψ r }
  obtain ⟨G, hG⟩ := (GlobalTheory.EtaleHensel.bijective_residue_comp R Q T).2 Ψ
  refine ⟨G.toRingHom, RingHom.ext fun r => G.commutes r, RingHom.ext fun q => ?_⟩
  exact DFunLike.congr_fun hG q

end GlobalTheory.NCyc.StrictLocLift

namespace GlobalTheory.NCyc.StrictLocLift

theorem exists_ringHom_of_isIndEtale {R S T : Type} [CommRing R] [CommRing S] [CommRing T] [HenselianLocalRing T]
    (a : R →+* S) (b : R →+* T) (ha : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale a) (ψ : S →+* ResidueField T)
    (hψ : ψ.comp a = (residue T).comp b) : ∃ g : S →+* T, g.comp a = b := by
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := ha
  have hts' : ∀ j, (s.app j).hom.comp (t.app j).hom = a := fun j => by
    have := congrArg CommRingCat.Hom.hom (hts j).2
    simpa using this
  have hψj : ∀ j, (ψ.comp (s.app j).hom).comp (t.app j).hom = (residue T).comp b := fun j => by
    rw [RingHom.comp_assoc, hts' j, hψ]
  choose g hg using fun j => lift_exists (t.app j).hom (hts j).1 b (ψ.comp (s.app j).hom) (hψj j)
  have nat : ∀ {j k : J} (u : j ⟶ k), (g k).comp (D.map u).hom = g j := by
    intro j k u
    have ht : (D.map u).hom.comp (t.app j).hom = (t.app k).hom := by
      have := congrArg CommRingCat.Hom.hom (t.naturality u)
      simpa using this.symm
    have hs' : (s.app k).hom.comp (D.map u).hom = (s.app j).hom := by
      have e : D.map u ≫ s.app k = s.app j := by
        have := s.naturality u
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at this
        exact this
      have := congrArg CommRingCat.Hom.hom e
      rwa [CommRingCat.hom_comp] at this
    apply lift_unique (t.app j).hom (hts j).1 b
    · rw [RingHom.comp_assoc, ht, (hg k).1]
    · exact (hg j).1
    · rw [← RingHom.comp_assoc, (hg k).2, RingHom.comp_assoc, hs', (hg j).2]
  let c : Cocone D :=
    { pt := CommRingCat.of T
      ι := { app := fun j => CommRingCat.ofHom (g j)
             naturality := fun j k u => by
               ext q
               simpa using DFunLike.congr_fun (nat u) q } }
  refine ⟨(hs.desc c).hom, ?_⟩
  obtain ⟨j⟩ : Nonempty J := IsFiltered.nonempty
  have hf : (hs.desc c).hom.comp (s.app j).hom = g j := by
    have := congrArg CommRingCat.Hom.hom (hs.fac c j)
    simpa [c] using this
  rw [← hts' j, ← RingHom.comp_assoc, hf, (hg j).1]

end GlobalTheory.NCyc.StrictLocLift

namespace GlobalTheory.NCyc.StrictLocLift

theorem exists_ringHom_of_isStrictHenselisation {R S T : Type} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] [CommRing T] [HenselianLocalRing T] [IsSepClosed (ResidueField T)]
    (a : R →+* S) (ha : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation a) (b : R →+* T) [IsLocalHom b] :
    ∃ g : S →+* T, g.comp a = b := by
  letI : Algebra R S := a.toAlgebra
  haveI : IsLocalHom (algebraMap R S) := ha.2.2.1
  obtain ⟨-, -, hsep⟩ := GlobalTheory.IndEtaleLocal.flat_map_maximalIdeal_isSeparable R S ha.2.2.2
  letI : Algebra (ResidueField R) (ResidueField T) := (ResidueField.map b).toAlgebra
  let ι : ResidueField S →ₐ[ResidueField R] ResidueField T := IsSepClosed.lift
  refine exists_ringHom_of_isIndEtale a b ha.2.2.2 (ι.toRingHom.comp (residue S)) (RingHom.ext fun r => ?_)
  have h1 : residue S (a r) = algebraMap (ResidueField R) (ResidueField S) (residue R r) := rfl
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [h1, ι.commutes]
  rfl

theorem lift : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) {x : X} (L : GlobalTheory.NCyc.StrictLoc X x)
    (M : GlobalTheory.NCyc.StrictLoc Y (f x)), ∃ h : L.scheme ⟶ M.scheme, h ≫ M.toX = L.toX ≫ f := by
  intro X Y f x L M
  haveI : IsLocalHom L.φ := L.isStrictHenselisation.2.2.1
  haveI : HenselianLocalRing L.A := L.henselian
  haveI : IsSepClosed (ResidueField L.A) := L.isSepClosed
  haveI : IsLocalHom (L.φ.comp (f.stalkMap x).hom) := inferInstance
  obtain ⟨g, hg⟩ := exists_ringHom_of_isStrictHenselisation M.φ M.isStrictHenselisation (L.φ.comp (f.stalkMap x).hom)
  refine ⟨Spec.map (CommRingCat.ofHom g), ?_⟩
  have e : CommRingCat.ofHom M.φ ≫ CommRingCat.ofHom g = f.stalkMap x ≫ CommRingCat.ofHom L.φ := by
    ext r; exact DFunLike.congr_fun hg r
  simp only [GlobalTheory.NCyc.StrictLoc.toX, Category.assoc]
  rw [← Category.assoc (Spec.map _), ← Spec.map_comp, e]
  have key : Spec.map (f.stalkMap x ≫ CommRingCat.ofHom L.φ) =
      Spec.map (CommRingCat.ofHom L.φ) ≫ Spec.map (f.stalkMap x) := Spec.map_comp _ _
  rw [key, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]

end GlobalTheory.NCyc.StrictLocLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.H0TateDualNoInvariantsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H0_coefRep_T2_subtype_eq_bot_of_noInv_matT : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (Dg : Subgroup (G H.E N.Om)), GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.NoInv Dg (GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matT N i ρ) → H0 ((Formalism.MainNotions.N.coefRep (Formalism.MainNotions.N.Glob.T2 N i ρ) (Kf N i)).comp Dg.subtype) = ⊥ := by
  first | exact @GlobalTheory.TateDualCoef.H0_coefRep_T2_comp_subtype_eq_bot_of_noInv | exact GlobalTheory.TateDualCoef.H0_coefRep_T2_comp_subtype_eq_bot_of_noInv | (intros; apply GlobalTheory.TateDualCoef.H0_coefRep_T2_comp_subtype_eq_bot_of_noInv <;> assumption)
end

