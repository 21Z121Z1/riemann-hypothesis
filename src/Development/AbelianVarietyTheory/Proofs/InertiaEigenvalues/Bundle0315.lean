import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0218
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0066
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0300
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulIntegralBis
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.Isog

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem latHom_ext {T T' : LocLat G Qp LL O} {u w : LatHom T.L T'.L} (h : u.f = w.f) : u = w := by
  cases u; cases w; cases h; rfl

theorem exists_quasi_inverse (c : O)
    (hc : ∀ a : LL, ∃ (k : ℕ) (b : O), algebraMap O LL b = algebraMap O LL c ^ k * a)
    {T' T : LocLat G Qp LL O} (f : LatHom T'.L T.L) (hf : Function.Bijective f.f) :
    ∃ (m : ℕ) (g : LatHom T.L T'.L), latComp g f = latSmul T' (c ^ m) ∧
      latComp f g = latSmul T (c ^ m) := by
  let e : T'.V ≃ₗ[LL] T.V := LinearEquiv.ofBijective f.f hf
  have he : ∀ g y, e.symm (T.ρ g y) = T'.ρ g (e.symm y) := by
    intro g y
    apply e.injective
    rw [e.apply_symm_apply]
    have := f.equiv g (e.symm y)
    change e _ = T.ρ g (e _) at this
    rw [this, e.apply_symm_apply]
  obtain ⟨m, hm⟩ := GlobalTheory.WachSat.exists_pow_smul_le (LL := LL) c hc T'.L.T
    (T.L.T.map (e.symm.toLinearMap.restrictScalars O)) T'.L.span (T.L.fg.map _)
  haveI : ContinuousSMul LL T'.V := IsModuleTopology.toContinuousSMul LL T'.V
  let g : LatHom T.L T'.L :=
    { f := algebraMap O LL (c ^ m) • e.symm.toLinearMap
      equiv := fun g y => by simp [he]
      cont := IsModuleTopology.continuous_of_linearMap _
      T_le := fun y hy => by
        have := hm _ (Submodule.mem_map_of_mem hy)
        rw [← algebraMap_smul LL] at this
        exact this }
  refine ⟨m, g, latHom_ext ?_, latHom_ext ?_⟩
  · ext y
    change algebraMap O LL (c ^ m) • e.symm (e y) = algebraMap O LL (c ^ m) • y
    rw [e.symm_apply_apply]
  · ext y
    change e (algebraMap O LL (c ^ m) • e.symm y) = algebraMap O LL (c ^ m) • y
    rw [map_smul, e.apply_symm_apply]

variable (W : LocWach PD LL O v n)

theorem dd_torsionFree (hp : ∀ a : O, (PD.p : O) * a = 0 → a = 0) (T : LocLat G Qp LL O) (m : ℕ)
    (x : W.DD T) (hx : ((PD.p : O) ^ m) • x = 0) : x = 0 := by
  have hreg : ∀ (k : ℕ) (y : W.EE), (PD.p : W.EE) ^ k * y = 0 → y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      exact ih y (GlobalTheory.WachSat.ee_torsionFree W hp _ (by rw [← hy]; ring))
  haveI := (W.DD_free T).1
  let b := Module.Free.chooseBasis W.EE (W.DD T)
  rw [← algebraMap_smul W.EE, map_pow, map_natCast] at hx
  apply b.repr.injective
  ext j
  have := congrArg (fun z => b.repr z j) hx
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at this
  simpa using hreg m _ this

theorem globalBasis_of_basis (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (b : Module.Basis (Fin (Module.finrank O ↥T.L.T)) (LetA O n) ↥(W.N T)) :
    GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.GlobalBasis W T := by
  let b' := (W.N_base T hT).basis b
  have hb : (fun j => (b j : W.DD T)) = b' := by
    funext j
    exact ((W.N_base T hT).basis_apply b j).symm
  refine ⟨b, ?_, ?_⟩
  · rw [hb]; exact b'.linearIndependent
  · rw [hb]; exact b'.span_eq

theorem isog_generic (hp : ∀ a : O, (PD.p : O) * a = 0 → a = 0)
    (hc : ∀ a : LL, ∃ (k : ℕ) (b : O), algebraMap O LL b = algebraMap O LL (PD.p : O) ^ k * a)
    (T' T : LocLat G Qp LL O) (f : LatHom T'.L T.L) (hT' : IsCrys PD T'.ρ) (hT : IsCrys PD T.ρ)
    (hs : ∀ (m : ℕ) (x : W.DD T'), ((PD.p : O) ^ m) • x ∈ W.N T' → x ∈ W.N T')
    (hf : Function.Bijective f.f) :
    Function.Injective (W.map f) ∧
    (∃ c : ℕ, ∀ y : W.DD T, ∃ x : W.DD T', W.map f x = ((PD.p : O) ^ c) • y ∧
      (y ∈ W.N T → x ∈ W.N T')) ∧
    ∀ x : W.DD T', W.map f x ∈ W.N T ↔ x ∈ W.N T' := by
  obtain ⟨m, g, hgf, hfg⟩ := exists_quasi_inverse (PD.p : O) hc f hf
  have h1 : ∀ x, W.map g (W.map f x) = ((PD.p : O) ^ m) • x := fun x => by
    rw [← W.map_comp, hgf, W.map_latSmul]
  have h2 : ∀ x, W.map f (W.map g x) = ((PD.p : O) ^ m) • x := fun x => by
    rw [← W.map_comp, hfg, W.map_latSmul]
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_,
    ⟨m, fun y => ⟨W.map g y, h2 y, W.map_N g hT hT' y⟩⟩,
    fun x => ⟨fun hx => hs m x ?_, W.map_N f hT' hT x⟩⟩
  · refine dd_torsionFree W hp T' m x ?_
    rw [← h1, hx, map_zero]
  · rw [← h1]
    exact W.map_N g hT hT' _ hx

end Generic

section Loc

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)

theorem p_regular (a : ↥(OL LL)) (ha : (((P.PD K).p : ℕ) : ↥(OL LL)) * a = 0) : a = 0 := by
  have hl0 : (l : ↥LL.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  rw [P.PD_p] at ha
  have : (l : ↥LL.1) * (a : ↥LL.1) = 0 := by
    have := congrArg (Subtype.val) ha
    simpa using this
  exact Subtype.ext ((mul_eq_zero.1 this).resolve_left hl0)

theorem exists_pow_mul_integral (a : ↥LL.1) : ∃ (k : ℕ) (b : ↥(OL LL)), algebraMap ↥(OL LL) ↥LL.1 b =
    algebraMap ↥(OL LL) ↥LL.1 (((P.PD K).p : ℕ) : ↥(OL LL)) ^ k * a := by
  rw [P.PD_p]
  have : ∃ k : ℕ, 0 ≤ P.v LL ((l : ↥LL.1) ^ k * a) := by
    cases hq : P.v LL a with
    | top => exact ⟨0, by simp [hq]⟩
    | coe q =>
      obtain ⟨k, hk⟩ := exists_nat_ge (-q)
      refine ⟨k, ?_⟩
      rw [AddValuation.map_mul, AddValuation.map_pow, P.v_l, hq, nsmul_one, ← WithTop.coe_natCast,
        ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]
      linarith
  obtain ⟨k, hk⟩ := this
  exact ⟨k, ⟨_, (P.v_O LL _).1 hk⟩, by rw [map_natCast]; rfl⟩

end Loc

section Main

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL)

theorem sat_loc (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) (m : ℕ) (x : (H.W K s LL h).DD T)
    (hx : ((((P.PD K).p : ℕ) : ↥(OL LL)) ^ m) • x ∈ (H.W K s LL h).N T) : x ∈ (H.W K s LL h).N T := by
  obtain ⟨b⟩ := N_basis_loc H K s LL h T hT
  exact GlobalTheory.WachSat.mem_of_pow_smul_mem _ (p_regular P K LL) T (globalBasis_of_basis _ T hT b) m x hx

theorem isog_loc (T' T : Lt K LL) (f : LatHom T'.L T.L) (hT' : IsCrys (P.PD K) T'.ρ)
    (hT : IsCrys (P.PD K) T.ρ) (hf : Function.Bijective f.f) :
    Function.Injective ((H.W K s LL h).map f) ∧
    (∃ c : ℕ, ∀ y : (H.W K s LL h).DD T, ∃ x : (H.W K s LL h).DD T',
      (H.W K s LL h).map f x = ((((P.PD K).p : ℕ) : ↥(OL LL)) ^ c) • y ∧
      (y ∈ (H.W K s LL h).N T → x ∈ (H.W K s LL h).N T')) ∧
    ∀ x : (H.W K s LL h).DD T', (H.W K s LL h).map f x ∈ (H.W K s LL h).N T ↔
      x ∈ (H.W K s LL h).N T' :=
  isog_generic (H.W K s LL h) (p_regular P K LL) (exists_pow_mul_integral P K LL) T' T f hT' hT
    (sat_loc H K s LL h T' hT') hf

end Main

end GlobalTheory.NL.Isog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalTatePairingBilinear
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.PairLine

section Cont

variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] [TopologicalSpace LL]
  [IsTopologicalRing LL]

theorem cont_form {V : Type} [AddCommGroup V] [Module LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [IsModuleTopology LL V] (f : V →ₗ[LL] LL) : Continuous f :=
  IsModuleTopology.continuous_of_linearMap f

theorem cont_act {V : Type} [AddCommGroup V] [Module LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [IsModuleTopology LL V] (ρ : Representation LL G V)
    (hρ : ∀ x, Continuous fun g => ρ g x) : Continuous fun p : G × V => ρ p.1 p.2 := by
  haveI : ContinuousSMul LL V := IsModuleTopology.toContinuousSMul LL V
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd LL V
  let b := Module.finBasis LL V
  have h : (fun p : G × V => ρ p.1 p.2) = fun p => ∑ i, b.repr p.2 i • ρ p.1 (b i) := by
    funext p
    conv_lhs => rw [← b.sum_repr p.2]
    simp only [map_sum, map_smul]
  rw [h]
  refine continuous_finset_sum _ fun i _ => ?_
  exact ((cont_form ((Finsupp.lapply i).comp b.repr.toLinearMap)).comp continuous_snd).smul
    ((hρ (b i)).comp continuous_fst)

theorem cont_bil {V V' : Type} [AddCommGroup V] [Module LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [IsModuleTopology LL V] [AddCommGroup V'] [Module LL V']
    [FiniteDimensional LL V'] [TopologicalSpace V'] [IsModuleTopology LL V']
    (m : V →ₗ[LL] V' →ₗ[LL] LL) : Continuous fun q : V × V' => m q.1 q.2 := by
  let b := Module.finBasis LL V
  have h : (fun q : V × V' => m q.1 q.2) = fun q => ∑ i, b.repr q.1 i * m (b i) q.2 := by
    funext q
    conv_lhs => rw [← b.sum_repr q.1]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul]
  rw [h]
  refine continuous_finset_sum _ fun i _ => ?_
  exact ((cont_form ((Finsupp.lapply i).comp b.repr.toLinearMap)).comp continuous_fst).mul
    ((cont_form (m (b i))).comp continuous_snd)

end Cont

theorem exists_pair : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∃ β : ↥(continuousCocycles A.ρ) →ₗ[LL] ↥(continuousCocycles A'.ρ) →ₗ[LL] LL, ∀ a b, β a b = 0 ↔ CobL (P.PD K) (cupL A'.ρ m a.1 b.1) := by
  intro hT l _ P K LL _ _ _ O _ _ hO A A' m hm
  obtain ⟨Z, inv, hZ, hinv⟩ := GlobalTheory.InvLine.exists_inv hT l P K LL O hO
  haveI : IsTopologicalRing LL := hO.2.2.2.1
  have hmem : ∀ (a : ↥(continuousCocycles A.ρ)) (b : ↥(continuousCocycles A'.ρ)), cupL A'.ρ m a.1 b.1 ∈ Z := by
    intro a b
    obtain ⟨ha, ha'⟩ : Continuous a.1 ∧ ∀ g h, a.1 (g * h) = a.1 g + A.ρ g (a.1 h) := a.2
    obtain ⟨hb, hb'⟩ : Continuous b.1 ∧ ∀ g h, b.1 (g * h) = b.1 g + A'.ρ g (b.1 h) := b.2
    rw [hZ]
    refine ⟨?_, fun g h k => ?_⟩
    · have h1 : Continuous fun p : ↥(GK K) × ↥(GK K) => A'.ρ p.1 (b.1 p.2) :=
        (cont_act A'.ρ A'.cont).comp (continuous_fst.prodMk (hb.comp continuous_snd))
      exact (cont_bil m).comp ((ha.comp continuous_fst).prodMk h1)
    · simp only [cupL]
      rw [← hm.1 g (a.1 h) (A'.ρ h (b.1 k)), ha', hb', map_mul, Module.End.mul_apply]
      simp only [map_add, LinearMap.add_apply]
      ring
  refine ⟨LinearMap.mk₂ LL (fun a b => inv ⟨cupL A'.ρ m a.1 b.1, hmem a b⟩) ?_ ?_ ?_ ?_,
    fun a b => ?_⟩
  · intro a a' b
    rw [← map_add]; congr 1; apply Subtype.ext; funext p
    simp [cupL]
  · intro c a b
    rw [← map_smul]; congr 1; apply Subtype.ext; funext p
    simp [cupL]
  · intro a b b'
    rw [← map_add]; congr 1; apply Subtype.ext; funext p
    simp [cupL]
  · intro c a b
    rw [← map_smul]; congr 1; apply Subtype.ext; funext p
    simp [cupL]
  · rw [LinearMap.mk₂_apply]
    exact hinv _

end GlobalTheory.PairLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistableTensorPairingOfDual
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon.StPairing

section

variable {F : Type} [Field F] {B : Type} [CommRing B] [Algebra F B]
  {V V' : Type} [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V']

def tensorPairing (m : V →ₗ[F] V' →ₗ[F] F) : V ⊗[F] B →ₗ[F] V' ⊗[F] B →ₗ[F] B :=
  (TensorProduct.map₂ m (LinearMap.mul F B)).compr₂ (TensorProduct.lid F B).toLinearMap

@[simp] theorem tensorPairing_tmul (m : V →ₗ[F] V' →ₗ[F] F) (v : V) (a : B) (v' : V') (b : B) :
    tensorPairing m (v ⊗ₜ[F] a) (v' ⊗ₜ[F] b) = m v v' • (a * b) := by
  simp [tensorPairing, TensorProduct.map₂_apply_tmul]

theorem tensorPairing_one (m : V →ₗ[F] V' →ₗ[F] F) (v : V) (y : V' ⊗[F] B) :
    tensorPairing m (v ⊗ₜ[F] (1 : B)) y = TensorProduct.lid F B (LinearMap.rTensor B (m v) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v' b => simp [tensorPairing_tmul]
  | add y y' hy hy' => simp only [map_add, hy, hy']

theorem induction_two {p : V ⊗[F] B → V' ⊗[F] B → Prop} (h0 : ∀ y, p 0 y) (h0' : ∀ x, p x 0)
    (ht : ∀ v a v' b, p (v ⊗ₜ[F] a) (v' ⊗ₜ[F] b))
    (ha : ∀ x x' y, p x y → p x' y → p (x + x') y)
    (ha' : ∀ x y y', p x y → p x y' → p x (y + y')) (x : V ⊗[F] B) (y : V' ⊗[F] B) : p x y := by
  induction x using TensorProduct.induction_on with
  | zero => exact h0 y
  | tmul v a =>
    induction y using TensorProduct.induction_on with
    | zero => exact h0' _
    | tmul v' b => exact ht v a v' b
    | add y y' hy hy' => exact ha' _ _ _ hy hy'
  | add x x' hx hx' => exact ha _ _ _ hx hx'

end

theorem exists_stPairing : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → ∃ pr : V ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bst P →ₗ[ℚ_[l]] Bst P, (∀ x y, pr (phiV P ℚ_[l] V x) (phiV P ℚ_[l] V' y) = phiSt P (pr x y)) ∧ (∀ x y, pr (monV P ℚ_[l] V x) y + pr x (monV P ℚ_[l] V' y) = monSt P (pr x y)) ∧ (∀ (g : ↥(GK K)) x y, pr (stRep P ρ g x) (stRep P ρ' g y) = ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) • actSt P (g : GQ l) (pr x y)) ∧ (∀ a x y, pr (onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) x) y = a * pr x y) ∧ ∀ y, (∀ v : V, pr (v ⊗ₜ[ℚ_[l]] (1 : Bst P)) y = 0) → y = 0 := by
  intro l _ P K V _ _ _ V' _ _ _ ρ ρ' m hm
  obtain ⟨hg, -, hr, -⟩ := hm
  have hcyc : ∀ g : ↥(GK K), ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l]) =
      ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) := fun g => by
    have h := P.PD_χ K g
    simp [cycLL, h]
  refine ⟨tensorPairing m, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    refine induction_two (p := fun x y => tensorPairing m (phiV P ℚ_[l] V x) (phiV P ℚ_[l] V' y) =
      phiSt P (tensorPairing m x y)) (by simp) (by simp) ?_ ?_ ?_ x y
    · intro v a v' b
      simp [tensorPairing_tmul, map_mul, map_smul]
    · intro x x' y hx hx'
      simp only [map_add, LinearMap.add_apply, hx, hx']
    · intro x y y' hy hy'
      simp only [map_add, hy, hy']
  · intro x y
    refine induction_two (p := fun x y => tensorPairing m (monV P ℚ_[l] V x) y +
      tensorPairing m x (monV P ℚ_[l] V' y) = monSt P (tensorPairing m x y)) (by simp) (by simp) ?_ ?_ ?_ x y
    · intro v a v' b
      simp only [monV_tmul, tensorPairing_tmul]
      rw [map_smul, ← smul_add]
      congr 1
      simp only [monSt_apply, Polynomial.derivative_mul]
      ring
    · intro x x' y hx hx'
      simp only [map_add, LinearMap.add_apply, ← hx, ← hx']
      abel
    · intro x y y' hy hy'
      simp only [map_add, ← hy, ← hy']
      abel
  · intro g x y
    refine induction_two (p := fun x y => tensorPairing m (stRep P ρ g x) (stRep P ρ' g y) =
      ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) • actSt P (g : GQ l) (tensorPairing m x y))
      (by simp) (by simp) ?_ ?_ ?_ x y
    · intro v a v' b
      rw [stRep_tmul, stRep_tmul, tensorPairing_tmul, tensorPairing_tmul, hg, hcyc, map_smul, map_mul,
        smul_smul]
    · intro x x' y hx hx'
      simp only [map_add, LinearMap.add_apply, hx, hx', smul_add]
    · intro x y y' hy hy'
      simp only [map_add, hy, hy', smul_add]
  · intro a x y
    refine induction_two (p := fun x y => tensorPairing m (onB P ℚ_[l] V (LinearMap.mulLeft ℚ_[l] a) x) y =
      a * tensorPairing m x y) (by simp) (by simp) ?_ ?_ ?_ x y
    · intro v b v' c
      rw [onB_tmul, tensorPairing_tmul, tensorPairing_tmul, LinearMap.mulLeft_apply, mul_smul_comm,
        mul_assoc]
    · intro x x' y hx hx'
      simp only [map_add, LinearMap.add_apply, hx, hx', mul_add]
    · intro x y y' hy hy'
      simp only [map_add, hy, hy', mul_add]
  · intro y hy
    refine GlobalTheory.T.eq_zero_of_rTensor_pairing_eq_zero ℚ_[l] (Bst P) V V' m hr y fun v => ?_
    rw [← tensorPairing_one]
    exact hy v

end GlobalTheory.PMon.StPairing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTateTwistDualPerfectPairing
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module

noncomputable section
namespace GlobalTheory.DualTwist

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l)
  {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]

def dualEquiv : (Fin (finrank ℚ_[l] V) → ℚ_[l]) ≃ₗ[ℚ_[l]] Module.Dual ℚ_[l] V :=
  (Module.finBasis ℚ_[l] V).dualBasis.equivFun.symm

theorem dualEquiv_basis (z : Fin (finrank ℚ_[l] V) → ℚ_[l]) (i : Fin (finrank ℚ_[l] V)) :
    dualEquiv z (Module.finBasis ℚ_[l] V i) = z i := by
  simp [dualEquiv, Basis.equivFun_symm_apply, Finset.sum_apply, Basis.dualBasis_apply_self, Finsupp.single_apply]

theorem dualEquiv_symm_apply (f : Module.Dual ℚ_[l] V) (i : Fin (finrank ℚ_[l] V)) :
    (dualEquiv (V := V)).symm f i = f (Module.finBasis ℚ_[l] V i) := by
  conv_rhs => rw [← (dualEquiv (V := V)).apply_symm_apply f]
  rw [dualEquiv_basis]

def chiS (g : ↥(GK K)) : ℚ_[l] := ((cycLL (P.PD K) ℚ_[l] g : ℚ_[l]ˣ) : ℚ_[l])

theorem chiS_mul (g h : ↥(GK K)) : chiS P K (g * h) = chiS P K g * chiS P K h := by
  simp [chiS]

theorem chiS_one : chiS P K 1 = 1 := by simp [chiS]

def dualOp (ρ : Representation ℚ_[l] ↥(GK K) V) (g : ↥(GK K)) :
    (Fin (finrank ℚ_[l] V) → ℚ_[l]) →ₗ[ℚ_[l]] (Fin (finrank ℚ_[l] V) → ℚ_[l]) where
  toFun y := chiS P K g • (dualEquiv (V := V)).symm ((dualEquiv y).comp (ρ g⁻¹))
  map_add' y z := by simp [LinearMap.add_comp, smul_add]
  map_smul' c y := by simp [LinearMap.smul_comp, smul_comm c]

theorem dualEquiv_dualOp (ρ : Representation ℚ_[l] ↥(GK K) V) (g : ↥(GK K)) (y) :
    dualEquiv (dualOp P K ρ g y) = chiS P K g • (dualEquiv y).comp (ρ g⁻¹) := by
  simp [dualOp]

def dualRep (ρ : Representation ℚ_[l] ↥(GK K) V) :
    Representation ℚ_[l] ↥(GK K) (Fin (finrank ℚ_[l] V) → ℚ_[l]) where
  toFun g := dualOp P K ρ g
  map_one' := by
    refine LinearMap.ext fun y => ?_
    apply (dualEquiv (V := V)).injective
    rw [dualEquiv_dualOp]
    simp [chiS_one, Module.End.one_eq_id]
  map_mul' g h := by
    refine LinearMap.ext fun y => ?_
    apply (dualEquiv (V := V)).injective
    rw [Module.End.mul_apply, dualEquiv_dualOp, dualEquiv_dualOp, dualEquiv_dualOp, chiS_mul,
      mul_inv_rev, map_mul, Module.End.mul_eq_comp, LinearMap.smul_comp, smul_smul, LinearMap.comp_assoc]

def dualPair : V →ₗ[ℚ_[l]] (Fin (finrank ℚ_[l] V) → ℚ_[l]) →ₗ[ℚ_[l]] ℚ_[l] :=
  (dualEquiv (V := V)).toLinearMap.flip

theorem dualPair_apply (x : V) (y : Fin (finrank ℚ_[l] V) → ℚ_[l]) : dualPair x y = dualEquiv y x := rfl

end GlobalTheory.DualTwist

namespace GlobalTheory.DualTwist
variable {l : ℕ} [Fact l.Prime]

theorem chiS_eq (P : LocPrime l) (K : FinExt l) (g : ↥(GK K)) :
    chiS P K g = (P.χQ (g : GQ l) : ℚ_[l]) := by
  simp [chiS, cycLL, P.PD_χ]

theorem chiS_cont (P : LocPrime l) (K : FinExt l) : Continuous (chiS P K) := by
  have h : chiS P K = fun g : ↥(GK K) => (P.χQ (g : GQ l) : ℚ_[l]) := funext (chiS_eq P K)
  rw [h]
  exact (GlobalTheory.Cyc.IsCyc.continuous P.χQ_cyc).comp continuous_subtype_val

theorem exists_dual1 : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v, Continuous fun g => ρ g v) → ∃ (ρ' : Representation ℚ_[l] ↥(GK K) (Fin (finrank ℚ_[l] V) → ℚ_[l])) (m : V →ₗ[ℚ_[l]] (Fin (finrank ℚ_[l] V) → ℚ_[l]) →ₗ[ℚ_[l]] ℚ_[l]), (∀ y, Continuous fun g => ρ' g y) ∧ IsDual1 (P.PD K) ρ ρ' m := by
  intro l _ P K V _ _ _ _ _ _ _ ρ hc
  refine ⟨dualRep P K ρ, dualPair, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    apply continuous_pi
    intro i
    have h : (fun g : ↥(GK K) => dualRep P K ρ g y i) =
        fun g => chiS P K g * dualEquiv y (ρ g⁻¹ (Module.finBasis ℚ_[l] V i)) := by
      funext g
      change dualOp P K ρ g y i = _
      simp [dualOp, dualEquiv_symm_apply]
    rw [h]
    have hy : Continuous (dualEquiv (V := V) y) :=
      IsModuleTopology.continuous_of_linearMap (dualEquiv (V := V) y)
    exact (chiS_cont P K).mul (hy.comp ((hc _).comp continuous_inv))
  · intro g x y
    change dualEquiv (dualOp P K ρ g y) (ρ g x) = chiS P K g * dualEquiv y x
    rw [dualEquiv_dualOp, LinearMap.smul_apply, LinearMap.comp_apply, ← Module.End.mul_apply,
      ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, smul_eq_mul]
  · intro x hx
    apply (Module.finBasis ℚ_[l] V).forall_coord_eq_zero_iff.mp
    intro i
    have := hx ((dualEquiv (V := V)).symm ((Module.finBasis ℚ_[l] V).coord i))
    rwa [dualPair_apply, LinearEquiv.apply_symm_apply] at this
  · intro y hy
    funext i
    exact (dualEquiv_basis y i).symm.trans (hy _)
  · simp

end GlobalTheory.DualTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusTensorCrisToSemistableComm
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem phiV_crisIncl_comm : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (w : V ⊗[ℚ_[l]] P.R.B), phiV P ℚ_[l] V (crisIncl P ℚ_[l] V w) = crisIncl P ℚ_[l] V (φVB (P.PD K) (LL := ℚ_[l]) (V := V) w) := by
  intro l _ P K V _ _ w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    simp only [crisIncl_tmul, phiV_tmul, phiSt_C, φVB, AlgebraTensorModule.map_tmul,
      LinearMap.id_apply, AlgHom.toLinearMap_apply, P.PD_φ K b]
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTracePatternIdempotentExchangeStatement
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupAlgebraTrace_patternIdempotent_exchange : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ), N = k + 2 * s + 1 → ∀ χ : Gn g N → ℂ, IsClass χ → tr (eJ g N k s ψ) χ = tr (eJ' g N k ψ) χ := by
  first | exact @GlobalTheory.GLq.tr_eJ_eq_tr_eJ' | exact GlobalTheory.GLq.tr_eJ_eq_tr_eJ' | (intros; apply GlobalTheory.GLq.tr_eJ_eq_tr_eJ' <;> assumption)
end

